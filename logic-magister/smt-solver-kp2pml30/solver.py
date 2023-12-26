import sys
from threading import Event
from utils import read_DIMACS, SATSolverResult
from z3 import *


class Solver:
    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.variables_count, self.clauses = read_DIMACS(filename)

    def encode(self):
        """
        Ваша задача: закодировать SAT при помощи теории массивов.
        В self.clauses хранятся обычные DIMACS SAT дизъюнкты.
        :return Ваша задача вернуть список (конъюнкцию) литералов в теории QF_ALIA (массивы с линейной целочисленной арифметикой)
            такую, что она выполнима в теории QF_ALIA тогда и только тогда, когда self.clauses выполнимо в логике высказываний
        Замечание: в данной функции вы должны по одним формулам породить другие, создавать новые решатели запрещено
        Замечание: обратите внимание на функцию K в Z3 API, которая позволяет создавать константные массивы, например K(IntSort(), 42)
        Замечание: если хотите поупражняться, можете решить чуть более сложную задачу: сделать то же самое, не используя арифметику
                   для этого измените код ниже на `array_solver = SolverFor("QF_AX")`
        """
        # print(self.clauses)
        vars = Array('A', IntSort(), IntSort())
        res = []
        for i in range(self.variables_count):
            v = vars[i]
            res.append(v >= 0)
            res.append(v <= 1)
        m_and = lambda x, y: x * y
        m_or = lambda x, y: x + y - x * y
        m_not = lambda x: 1 - x
        big_or = lambda a: sum(a) > 0
        for clause in self.clauses:
            ors = []
            for var in clause:
                assert var != 0
                v = vars[abs(var) - 1]
                if var < 0:
                    v = m_not(v)
                ors.append(v)
            res.append(big_or(ors))
        # print(res)
        return res

    def solve(self) -> SATSolverResult:
        array_formulas = list(self.encode())
        if self.sigkill.is_set():
            return SATSolverResult.UNKNOWN
        array_solver = SolverFor("QF_ALIA")
        array_solver.set(timeout=10 * 1000)
        array_solver.add(array_formulas)
        # print(array_solver.to_smt2())
        result = array_solver.check()
        if result == sat:
            # print(array_solver.model())
            return SATSolverResult.SAT
        elif result == unsat:
            return SATSolverResult.UNSAT
        return SATSolverResult.UNKNOWN


if __name__ == "__main__":
    result = Solver("tests/unsat-dpll/f0020-03-u.cnf", Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")
