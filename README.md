# no-three-in-a-line-z3py
CS2800 Spring 2021 - Final Project 

This is a project which aims to find solutions to the [No Three in a Line problem](https://en.wikipedia.org/wiki/No-three-in-line_problem) through SMT reduction. The aim of this project is to demonstrat how SMT reduction (through the Z3Py library) can be used to produce solutions which contain the maximum number of *2n* points for small values of *n*. For this reason, the constraints are hard-coded to look for solutions which contain exactly *2n* points, even though the current known asymptotic upper bound is (1-eps)n.

This code does not feature any optimizations for symmetry, so the largest value of *n* that can be calculated before the exponential runtime grows beyond reasonable limits is n=8. For reference, the largest value of *n* where solutions of *2n* points is known for is n=46.

A list of solutions (drawn in ASCII) that were obtained from this code can be seen in solutions.txt.  

Instructions:
Install z3py with pip (recommended to do so in a virtual environment, see https://docs.python.org/3/library/venv.html for instructions):
``` pip install z3-solver ```

Run with the desired positive integral N (recommended no larger than 8):
``` py ntial.py <N> ```

To run tests:
``` py tests.py ```
