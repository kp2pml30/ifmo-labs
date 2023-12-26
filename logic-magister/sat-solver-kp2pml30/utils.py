#!/usr/bin/env python3
from enum import Enum


class SATSolverResult(Enum):
    SAT = 1
    UNSAT = 2
    UNKNOWN = 3


def read_DIMACS(fname):
    def read_text_file(fname):
        with open(fname) as f:
            content = f.readlines()
        return [x.strip() for x in content]

    content = [line for line in read_text_file(fname) if line and not line.startswith("c")]

    header = content[0].split(" ")

    assert header[0] == "p" and header[1] == "cnf", content
    variables_total, clauses_total = int(header[2]), int(header[3])

    # array idx=number (of line) of clause
    # val=list of terms
    # term can be negative signed integer
    clauses = []
    for c in content[1:]:
        if c.startswith("c "):
            continue
        clause = []
        for var_s in c.split(None):
            var = int(var_s)
            if var != 0:
                clause.append(var)

        clauses.append(clause)

    if clauses_total != len(clauses):
        print("warning: header says ", clauses_total, " but read ", len(clauses))
    return variables_total, clauses
