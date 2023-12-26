import sys
from threading import Event
from utils import read_DIMACS, SATSolverResult

class State:
    def __init__(self, clauses):
        if clauses is None:
            return
        self.clauses = {}
        for i, cl in enumerate(clauses):
            self.clauses[i] = set(cl)
        self.vars = {}
        for i, cl in self.clauses.items():
            for var in cl:
                self.vars.setdefault(abs(var), (set(), set()))[0 if var > 0 else -1].add(i)
    def clone(self):
        ret = State(None)
        ret.clauses = { i: set(cl) for i, cl in self.clauses.items() }
        ret.vars = { vr: (set(d[0]), set(d[1])) for vr, d in self.vars.items() }
        return ret
    def set_true(self, var):
        avar = abs(var)
        for k in list(self.clauses.keys()):
            clause = self.clauses[k]
            if var in clause:
                self.clauses.pop(k)
                for ovar in clause:
                    aovar = abs(ovar)
                    self.vars[aovar][0].discard(k)
                    self.vars[aovar][1].discard(k)
            else:
                clause.discard(-var)
                self.vars[avar][0].discard(k)
                self.vars[avar][1].discard(k)

class Solver:
    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.variables_count, self.clauses = read_DIMACS(filename)
        self.known = {}
        self.un_pure = set()
        self.bad = []

    def solve(self) -> SATSolverResult:
        return self.solveImpl(State(self.clauses))

    def solveImpl(self, state) -> SATSolverResult:
        if self.sigkill.is_set():
            return SATSolverResult.UNKNOWN

        #print('1.', clauses)

        changed = True
        while changed:
            changed = False
            # units
            retr = True
            while retr:
                retr = False
                for clause in state.clauses.values():
                    if len(clause) == 1:
                        [el] = clause
                        state.set_true(el)
                        retr = True
                        break
                    elif len(clause) == 0:
                        return SATSolverResult.UNSAT

            # pures
            bad = self.bad
            bad.clear()
            for vr, st in state.vars.items():
                l_v = len(st[0])
                l_n = len(st[1])
                if l_v + l_n > 0:
                    if l_v != 0:
                        if l_n == 0:
                            state.set_true(vr)
                            changed = True
                    else:
                        state.set_true(-vr)
                        changed = True
                else:
                    bad.append(vr)
            # remove empty vars
            for vr in bad:
                state.vars.pop(vr, None)

        # check conditions
        if len(state.clauses) == 0:
            return SATSolverResult.SAT
        for x in state.clauses.values():
            if len(x) == 0:
                return SATSolverResult.UNSAT

        best_len = 10**9
        try_var = None
        for clause in state.clauses.values():
            if len(clause) < best_len:
                best_len = len(clause)
                try_var = next(iter(clause))
        # try_var = next(iter(next(iter(state.clauses.values()))))
        copy = state.clone()
        state.set_true(try_var)
        res = self.solveImpl(state)
        if res == SATSolverResult.SAT:
            return res
        state = copy
        state.set_true(-try_var)
        return self.solveImpl(state)


def main():
    result = Solver(sys.argv[1], Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")

if __name__ == "__main__":
    import cProfile
    cProfile.run('main()')
    main()
