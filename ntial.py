from z3 import *
from itertools import combinations


# Board: NxN grid with 0 for no piece, 1 for a piece
# Constraints: No three pieces may be colinear
# i.e., for any points ([x1, y1], [x2, y2]), board([m(x2-x1) + x1], [m(y2-y1) + y1]) == 0 for all m.

# a board is represented by a


class Grid:
    """Class for representing an NxN grid
    Also provides a function to print the grid
    """

    def __init__(self, N, instance=None):
        """
        instance is a string of n*n integers [0,1] representing an instance of the grid.
        0 means no point at that index, 1 means point at the index
        """
        self.N = N
        self.grid = [[False for col in range(N)] for row in range(N)]
        if instance:
            if len(instance) != N * N:
                raise ValueError(
                    str(N)
                    + "*"
                    + str(N)
                    + " grid should have "
                    + str(N * N)
                    + " items, got "
                    + str(len(instance))
                )
            for row in range(N):
                for col in range(N):
                    if instance[row * N + col] == "1":
                        self.grid[row][col] = True

    def points(self):
        """
        Returns a list of (x,y) tuples representing the coordinates of filled points on the grid.
        (0,0) is the bottom-left corner of the grid.
        """
        return [
            (col, row)
            for col in range(self.N)
            for row in range(self.N)
            if self.grid[row][col]
        ]

    def columns(self):
        """
        Returns a column-wise list of the points in each column.
        grid.columns()[c] lists all the points for x = c.
        Point (0, 0) is the bottom left corner.
        """
        return [
            [(col, row) for row in range(self.N) if self.grid[row][col]]
            for col in range(self.N)
        ]

    def print(self):
        """
        Prints the grid, with +y direction up and +x direction right.
        Point (0, 0) is the bottom left corner.
        """
        stack = []
        for row in range(self.N):
            line = ""
            for col in range(self.N):
                line += "1" if self.grid[row][col] else "0"
            stack.append(line)
        # print in reverse order so positive y is up instead of down
        while len(stack) > 0:
            print(stack.pop())


def construct_grid_from_model(N, solver):
    """ given the solver, check it for satisfiability and construct it as an NxN grid. """
    if solver.check() == sat:
        m = solver.model()
        grid_string_list = ["0" for i in range(N * N)]
        # if satisfiable, then there MUST be exactly 2*N points in the model
        for i in range(2 * N):
            x_i = Int("x_{0}".format(i))
            y_i = Int("y_{0}".format(i))
            xval = m.eval(x_i).as_long()
            yval = m.eval(y_i).as_long()
            grid_string_list[yval * N + xval] = "1"
        return Grid(N, "".join(grid_string_list))
    else:
        print("solver returned unsat, cannot create grid")
        return None


def three_solve(N):
    """Uses a z3 solver to check that no three points in the grid are colinear."""
    # y = mx + b
    solver = Solver()

    # strategy:
    # add 2n points
    # add (2n choose 2) lines between 2n points
    # add ((2n choose 2) permute 3) lines such that the length no of 2 lines sums to the length of the 3rd line

    # look for a solution with 2*N points (maximum number per pigeonhole principle)

    # add 2N unique points to the model
    for i in range(2 * N):
        x_i = Int("x_{0}".format(i))
        y_i = Int("y_{0}".format(i))
        tup = (x_i, y_i)
        # assert that every point is in the grid
        solver.add(And(x_i >= 0, x_i < N))
        solver.add(And(y_i >= 0, y_i < N))
        # assert that every point is unique
        distinct_points_assertations = []
        for j in range(2 * N):
            if i != j:
                x_j = Int("x_{0}".format(j))
                y_j = Int("y_{0}".format(j))
                distinct_points_assertations.append(Or(x_i != x_j, y_i != y_j))
        solver.add(And(distinct_points_assertations))

    # create (2*N choose 3) combinations of points
    points_indices = []
    for i in range(0, 2 * N - 2):
        for j in range(i + 1, 2 * N - 1):
            for k in range(j + 1, 2 * N):
                if i != j and j != k and k != i:
                    tup = (i, j, k)
                    points_indices.append(tup)

    # for each triplet, assert that the area created by the triangle is not 0
    # an area of a triangle is 0 iff the three points are colinear
    # an area of a triangle is given by:
    #                                 [ [ 1,  1,  1],
    #  A(p1, p2, p3) = 1/2 * Abs(Det(   [x1, x2, x3],  ))
    #                                   [y1, y2, y3] ]
    # (See derivation here https://people.richland.edu/james/lecture/m116/matrices/area.html)
    # so to assert that no three points are colinear, just assert that the det is not 0
    # equivalently: https://en.wikipedia.org/wiki/Shoelace_formula
    for triplet in points_indices:
        p1 = triplet[0]
        p2 = triplet[1]
        p3 = triplet[2]
        x1 = Int("x_{0}".format(p1))
        y1 = Int("y_{0}".format(p1))
        x2 = Int("x_{0}".format(p2))
        y2 = Int("y_{0}".format(p2))
        x3 = Int("x_{0}".format(p3))
        y3 = Int("y_{0}".format(p3))
        # apologies for the strange formatting, don't know how to tell black formatter to not do this
        solver.add(
            0
            != (
                ((x2 * y3) - (x3 * y2))
                - ((x1 * y3) - (x3 * y1))
                + ((x1 * y2) - (x2 * y1))
            )
        )

    # print(solver.assertions())
    if solver.check() == sat:
        # print(solver.model())
        g = construct_grid_from_model(N, solver)
        g.print()
        return g
    else:
        print("unsat for N=" + N)
        return None


def is_valid(grid):
    # make sure no more than 2 points are in each vertical column
    for column in grid.columns():
        if len(column) > 2:
            print("GRID IS INVALID - 3 COLINEAR POINTS DETECTED")
            return False

    # every 2 points should form a unique line equation (not counting vertical lines)
    lines = {None}
    for points_tuple in combinations(grid.points(), 2):
        p1 = points_tuple[0]
        p2 = points_tuple[1]

        # y = mx + b
        delta_y = p2[1] - p1[1]
        delta_x = p2[0] - p1[0]

        if delta_x == 0:
            # skip all vertical lines since their slopes are undefined
            continue
        else:
            m = delta_y / delta_x

        b = p1[1] - (m * p1[0])

        line = (m, b)
        if line in lines:
            print("GRID IS INVALID - 3 COLINEAR POINTS DETECTED")
            return False
        else:
            lines.add(line)

    print("GRID IS VALID - NO THREE POINTS COLINEAR")
    return True


def naive(N):
    """Naively calculates the maximum number of pieces that can be placed on a board of size NxN
    such that no 3 pieces are colinear. This is O(2^N), since every possible placement (piece or
    no piece) is tested.

    Returns a list of boards
    """
    return False


def main(N):
    grid = three_solve(N)
    is_valid(grid)


if __name__ == "__main__":
    main(int(sys.argv[1]))
