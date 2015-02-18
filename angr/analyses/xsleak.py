#from ..analysis import Analysis
#from ..variableseekr import StackVariable
from sleak import SleakMeta
from ..surveyors import Explorer
import logging
import simuvex

l = logging.getLogger("analysis.xsleak")

class SExplorer(Explorer):
    """
    Abstract class for XSleak
    This is separated from the rest of the code to avoid multiple inheritence
    issues with Analysis
    """

    def explorer_init(self, *args, **kwargs):
        super(SExplorer, self).__init__(*args, **kwargs)
        self._last=0

    @property
    def done(self):
        """
        Overrides Explorer's done method to keep going until we find a leaking
        path (or the superclass method decides to stop for another reason).
        """
        # Only recheck if we found new paths
        if len(self.found) > self._last:
            self._last = len(self.found)
            x = self._check_path(self.found[-1])
            if x is not None:
                self.leaks.append(x)

        # Stop if we have enough paths
        if len(self.leaks) >= self.num_leaks:
                return True

        # Delegate the decision to the superclass's method
        return super(SExplorer, self).done


class XSleak(SleakMeta, SExplorer):
    """
    Stack leak detection based on Explorer (i.e., full symbolic execution).
    We identify stuff that look like addresses at runtime, and start tracking
    them from there, until we reach targets.
    """

    def __init__(self, mode=None, targets=None, istate=None, argc=None, num_leaks=1):

        self.prepare(istate=istate, targets=targets, mode=mode, argc=argc)
        self.num_leaks = num_leaks

       # bp = simuvex.BP(simuvex.BP_AFTER, instruction=0x400745)
       # self.ipath.state.inspect.add_breakpoint('instruction', bp)

        # Explorer wants a tuple of addresses
        find_addrs = tuple(self.targets.values())
        #super(XSleak, self).__init__(self._p, find=find_addrs, start=self.ipath, num_find=0)
        self.explorer_init(self._p, find=find_addrs, start=self.ipath, num_find=4)
        self.run()

        # SimInspect doesn't serialize well, so we get rid of it first
        for l in [self.leak] + self.leak.successors:
                l.state.release_plugin("inspector")
        self.result = self.leak

    @property
    def terminated_paths(self):
        return self.found

