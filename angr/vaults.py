import collections.abc
import contextlib
import threading
import tempfile
import weakref
import logging
import pickle
import shelve
import uuid
import os
import io

import claripy

l = logging.getLogger("angr.vault")

class WeakKeyValueDict(object):
    """
    A dict in which items are removed whenever either key or value are
    garbage-collected.
    """
    def __init__(self, *args, **kw):
        init_dict = dict(*args, **kw)
        
        self._d = weakref.WeakKeyDictionary(
            (key, self._create_value(key, value))
            for key, value in init_dict.items())

    def _create_value(self, key, value):
        key_weakref = weakref.ref(key)
        def value_collected(wr):
            #l.warning("deleting %s %s", wr(), key_weakref())
            try:
                del self._d[key_weakref()]
            # Weird stuff happens when claripy objects go in sets...
            except (AttributeError, TypeError) as e:
                l.warning("Ignoring exception %s when deleting %s %s", e, key_weakref(), key_weakref().__class__)
                pass

        return weakref.ref(value, value_collected)

    def __getitem__(self, key):
        return self._d[key]()
    
    def __setitem__(self, key, value):
        self._d[key] = self._create_value(key, value)

    def __delitem__(self, key):
        del self._d[key]

    def __len__(self):
        return len(self._d)

    def __cmp__(self, other):
        try:
            return cmp(sorted(self.items()),
                       sorted(other.items()))
        except AttributeError:
            return NotImplemented

    def __hash__(self):
        raise TypeError("%s objects not hashable" % (self.__class__.__name__,))

    def __contains__(self, key):
        return key in self._d

    def __iter__(self):
        return self.keys()

    def iterkeys(self):
        return self._d.keys()

    def keys(self):
        return list(self.iterkeys())

    def itervalues(self):
        for value in self._d.itervalues():
            yield value()

    def values(self):
        return list(self.itervalues())
    
    def iteritems(self):
        for key in self._d:
            yield self._d[key]()

    def items(self):
        return list(self.iteritems())

    def update(self, other):
        for key, value in other.iteritems():
            self[key] = value

    def __repr__(self):
        return repr(self._d)

    def clear(self):
        self._d.clear()

    def copy(self):
        return WeakKeyValueDict(self)

    def get(self, key, default=None):
        if key in self:
            return self[key]
        return default

    def has_key(self, key):
        return key in self

    def pop(self, key, *args):
        if args:
            return self._pop_with_default(key, *args)
        return self._pop(key)

    def _pop(self, key):
        return self._d.pop(key)()
    
    def _pop_with_default(self, key, default):
        if key in self:
            return self._d.pop(key)
        return default

    def popitem(self):
        key, value = self._d.popitem()
        return key, value()

    def setdefault(self, key, default):
        if key in self:
            return self[key]
        self[key] = default
        return default

class PersistentID:
    """
    This is a wrapper class just so we can track weak references to the ID
    """
    def __init__(self, name):
        self.name = name

    def encode(self, encoding):
        return self.name.encode(encoding)

    def __lt__(self, other):
        return self.name < other.name

    def __eq__(self, other):
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def __str__(self):
        return "PersistentId: %s" % self.name

class VaultPickler(pickle.Pickler):
    def __init__(self, vault, file, assigned_pid=None, assigned_object=None, *args, **kwargs):
        """
        A persistence-aware pickler.
        It will check for persistence of any objects except for those with IDs in 'assigned_objects'.
        """

        super().__init__(file, *args, **kwargs)
        self.vault = vault
        self.assigned_object = assigned_object
        self.assigned_pid = assigned_pid

    def persistent_id(self, obj):

        if obj is self.assigned_object:
            return None

        pid = self.vault._get_persistent_id(obj)
        if pid is None:
            return None

        # assigned_object depends on pid
        self.vault._deps.setdefault(self.assigned_pid, set()).add (pid)

        return self.vault._store(obj, pid)

class VaultUnpickler(pickle.Unpickler):
    def __init__(self, vault, file, *args, **kwargs):
        super().__init__(file, *args, **kwargs)
        self.vault = vault

    def persistent_load(self, pid):
        return self.vault._load(pid)

class Vault(collections.abc.MutableMapping):
    """
    The vault is a serializer for angr.
    """

    #
    # These MUST be overriden.
    #

    def _read_context(self, strid):
        """
        Should be a context that yields a pickle-read()able file object for the given id i.
        """
        raise NotImplementedError()

    def _write_context(self, strid):
        """
        Should be a context that yields a pickle-write()able file object for the given id i.
        """
        raise NotImplementedError()

    def keys(self):
        """
        Should return the IDs stored by the vault.
        """
        raise NotImplementedError()

    def _delete(self, strid):
        raise NotImplementedError()

    #
    # Persistance managers
    #

    def __init__(self):
        # map from pid to object
        self._object_cache = WeakKeyValueDict()
        # map from object to pid
        self._uuid_cache = WeakKeyValueDict()
        # map from oid to PersistentID
        self._pid_cache = weakref.WeakValueDictionary()
        # If the key is referenced, also reference the value
        self._deps = weakref.WeakKeyDictionary()
        self.stored = set() # explicitly stored objects
        self._weak_stored = weakref.WeakSet() # implicit
        self.hash_dedup = {
            claripy.ast.Base, claripy.ast.BV, claripy.ast.FP, claripy.ast.Bool, claripy.ast.Int, claripy.ast.Bits,
        }
        self.module_dedup = set() # {'claripy', 'angr', 'archinfo', 'pyvex' } # cle causes recursion
        self.uuid_dedup = { SimState, Project }
        self.unsafe_key_baseclasses = {
            claripy.ast.Base, SimType #, SimActionObject
        }

    def _string_id_to_persistent_id(self, strid):
        if strid not in self._pid_cache:
            tmp = PersistentID(strid)
            self._pid_cache[strid] = tmp

        return self._pid_cache[strid]

    def _get_persistent_id(self, o):
        """
        Determines a persistent ID for an object.
        Does NOT do stores.
        """

        if type(o) in self.hash_dedup:
            oid = self._string_id_to_persistent_id (o.__class__.__name__ + "-" + str(hash(o)))
            self._object_cache[oid] = o
            return oid

        if any(isinstance(o,c) for c in self.unsafe_key_baseclasses):
            return None

        #if type(o) in self.uuid_dedup:
        #    return self._get_id(o)
        try:
            if o.__class__.__module__.split('.')[0] in self.module_dedup or o.__class__ in self.uuid_dedup:
                if o in self._uuid_cache:
                    return self._uuid_cache[o]
                else:
                    oid = self._string_id_to_persistent_id (o.__class__.__name__.split(".")[-1] + '-' + str(uuid.uuid4()))
                    self._object_cache[oid] = o
                    self._uuid_cache[o] = oid
                    return oid

        except TypeError:
            #l.warning("Unable to get persistent id of %s", o)
            pass

        return None

    #
    # Other stuff
    #

    def is_stored(self, pid):
        """
        Checks if the provided id is already in the vault.
        """
        if pid in self._weak_stored:
            return True

        try:
            with self._read_context(pid.name):
                return True
        except (AngrVaultError, EOFError):
            return False

    def load(self, pid):
        return self._load(pid)

    def _load(self, pid):
        """
        Retrieves one object from the pickler with the provided id.

        :param pid: an ID to use
        """
        # l.debug("LOAD: %s", oid)
        try:
            # l.debug("... trying cached")
            return self._object_cache[pid]
        except KeyError:
            # l.debug("... cached failed")
            with self._read_context(pid.name) as u:
                # add newly loaded object into the object cache
                o = VaultUnpickler(self, u).load()
                self._object_cache[pid] = o
                return o

    def store(self, o):

        pid = self._get_persistent_id(o) or self._string_id_to_persistent_id("TMP-"+str(uuid.uuid4()))

        self.stored.add (pid)

        return self._store(o, pid)

    def _finalize(self, oid):
        l.debug("%s is no longer reachable in the vault; finalizing", oid)
        self._delete (oid)

    def _store(self, o, pid): #pylint:disable=redefined-builtin
        """
        Stores an object and returns its ID.

        :param o: the object
        :param pid: an ID to use
        """

        #l.warning("STORE: %s %s", o, pid)

        # this handles recursive and existing objects
        if pid in self._weak_stored:
            return pid

        if self.is_stored(pid):
            #l.warning("... already stored")
            return pid

        with self._write_context(pid.name) as output:
            weakref.finalize(pid, self._finalize, pid.name)
            self._weak_stored.add(pid)
            VaultPickler(self, output, assigned_pid=pid, assigned_object=o).dump(o)

        return pid


    def delete(self, pid):
        self.stored.remove (pid)

        # This will cause pid's object to become unreachable and
        # finalized, so there is no reason to call _delete

    def dumps(self, o):
        """
        Returns a serialized string representing the object, post-deduplication.

        :param o: the object
        """
        f = io.BytesIO()
        VaultPickler(self, f).dump(o)
        f.seek(0)
        return f.read()

    def loads(self, s):
        """
        Deserializes a string representation of the object.

        :param s: the string
        """
        f = io.BytesIO(s)
        return VaultUnpickler(self, f).load()

    def _clear_cache(self):

        self._object_cache.clear()
        self._uuid_cache.clear()
        self._pid_cache.clear()
        self._deps.clear()
        self.stored.clear()
        self._weak_stored.clear()

    @staticmethod
    def close():
        pass

    #
    # For MutableMapping.
    #

    def __setitem__(self, k, v):
        self._store(v, k)

    def __getitem__(self, k):
        return self.load(k)

    def __delitem__(self, k):
        return self.delete(k)

    def __iter__(self):
        return iter(self.keys())

    def __len__(self):
        return len(self.keys())

class VaultDict(Vault):
    """
    A Vault that uses a dictionary for storage.
    """
    def __init__(self, d=None):
        super().__init__()
        self._dict = { } if d is None else d

    @contextlib.contextmanager
    def _write_context(self, strid):
        f = io.BytesIO()
        yield f
        f.seek(0)
        self._dict[strid] = f.read()

    @contextlib.contextmanager
    def _read_context(self, strid):
        try:
            f = io.BytesIO(self._dict[strid])
            yield f
        except KeyError as e:
            raise AngrVaultError from e

    def _delete(self, oid):
        if oid in self._dict:
            l.debug("_deleting %s", oid)
            del self._dict[oid]
        else:
            l.warning("%s was not in _dict", oid)

    def is_stored(self, pid):
        return pid.name in self._dict

    def keys(self):
        return self._dict.keys()

class VaultDir(Vault):
    """
    A Vault that uses a directory for storage.
    """
    def __init__(self, d=None):
        super().__init__()
        self._dir = tempfile.mkdtemp() if d is None else d
        with contextlib.suppress(FileExistsError):
            os.makedirs(self._dir)

    @contextlib.contextmanager
    def _write_context(self, strid):
        with open(os.path.join(self._dir, strid), "wb") as o:
            yield o

    @contextlib.contextmanager
    def _read_context(self, strid):
        try:
            with open(os.path.join(self._dir, strid), "rb") as o:
                yield o
        except FileNotFoundError as e:
            raise AngrVaultError from e

    def keys(self):
        return os.listdir(self._dir)


class VaultShelf(VaultDict):
    """
    A Vault that uses a shelve.Shelf for storage.
    """
    def __init__(self, path=None):
        self._path = tempfile.mktemp() if path is None else path
        s = shelve.open(self._path, protocol=-1)
        super().__init__(s)

    def close(self):
        self._dict.close()


class VaultDirShelf(VaultDict):
    """
    A Vault that uses a directory for storage, where every object is stored into a single shelve.Shelf instance.
    VaultDir creates a file for each object. VaultDirShelf creates only one file for a stored object and everything
    else it references.
    """

    def __init__(self, d=None):
        super().__init__()
        self._d = tempfile.mkdtemp() if d is None else d
        self._dict = None  # will be initialized at each call to store() or load()
        self._lock = threading.Lock()  # protecting access to self._dict

    @contextlib.contextmanager
    def _locked_shelve(self, shelve_path):
        with self._lock:
            self._dict = shelve.open(shelve_path, protocol=-1)
            yield
            self._dict.close()
            self._dict = None
            self._clear_cache()

    def store(self, o):
        oid = self._get_persistent_id(o) or "TMP-"+str(uuid.uuid4())
        shelve_path = os.path.join(self._d, oid)
        with self._locked_shelve(shelve_path):
            super()._store(o, oid)
        return oid

    def load(self, oid):

        shelve_path = os.path.join(self._d, oid)
        with self._locked_shelve(shelve_path):
            o = super().load(oid)

        return o

    def keys(self):
        s = set()
        for n in os.listdir(self._d):
            if "." not in n:
                s.add(n)
            else:
                s.add(n[:n.rfind(".")])  # remove the suffix
        return s


from .errors import AngrVaultError
from .project import Project
from .sim_type import SimType
from .sim_state import SimState
