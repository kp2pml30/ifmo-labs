import os
from threading import Event, Thread
from solver import Solver
from time import perf_counter
from utils import SATSolverResult
from collections import defaultdict


class Tests:
    def __init__(self, TIME_LIMIT: float):
        self.results = defaultdict(lambda: SATSolverResult.UNKNOWN)
        self.TIME_LIMIT = TIME_LIMIT
        self.tests_dir = os.path.join(os.getcwd(), "tests")

    def worker(self, path, event):
        self.results[path] = Solver(path, event).solve()

    def runner(self, path):
        event = Event()
        thread = Thread(target=self.worker, args=(path, event))
        t1 = perf_counter()
        thread.start()
        thread.join(self.TIME_LIMIT)
        event.set()
        thread.join()
        delta_t = perf_counter() - t1
        return delta_t

    def test_folder(self, folder: str, gold_result: SATSolverResult):
        for entry in os.scandir(os.path.join(self.tests_dir, folder)):
            print("Solving", entry.path)
            delta_t = self.runner(entry.path)
            result = self.results[entry.path]
            assert delta_t <= self.TIME_LIMIT
            if result != gold_result:
                print(result, 'vs gold =', gold_result)
            assert result == gold_result

    def rank_solver(self, tests):
        for folder, gold_result in tests:
            self.test_folder(folder, gold_result)

    def test_dpll(self):
        self.rank_solver([("sat-dpll", SATSolverResult.SAT), ("unsat-dpll", SATSolverResult.UNSAT)])


def SAT_to_Array_tests():
    Tests(TIME_LIMIT=10.0).test_dpll()

if __name__ == "__main__":
    SAT_to_Array_tests()
    print("tests done")
