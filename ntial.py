from z3 import *
from itertools import combinations
from time import perf_counter

# Board: NxN grid with 0 for no piece, 1 for a piece
# Constraints: No three pieces may be colinear
# i.e., for any points ([x1, y1], [x2, y2]), board([m(x2-x1) + x1], [m(y2-y1) + y1]) == 0 for all m.

# a board is represented by a


class Grid:
    """Class for representing an NxN grid."""

    def __init__(self, N, instance=None):
        """Constructs a Grid object.

        Args:
            N: the dimensions (number of rows and columns) of the grid.
            instance: an optional string from which the grid should fill in points. The string
                should have N^2 binary digits, where "0" indicates no point and "1" indicates a
                point at that coordinate. The grid is built "upwards" row by row.

                Example: Grid(2, "0111") constucts a grid with points (0, 1), (1, 0), and (1, 1).

        Returns:
            A grid object.

        Raises:
            ValueError: a syntax errror prevented the grid from being constructed by the instance.
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
                    + " digits, got "
                    + str(len(instance))
                )
            for char in instance:
                if char not in "01":
                    raise ValueError("provided instance is not a binary string")
            for row in range(N):
                for col in range(N):
                    if instance[row * N + col] == "1":
                        self.grid[row][col] = True

    def points(self):
        """Gets the list of populated points in this grid.

        (0,0) is the bottom-left corner of the grid.

        Returns:
            A list of (x,y) tuples representing the coordinates of filled points on the grid.

            Example: A grid which looks like
                01
                10
                returns the list [(0, 1), (1, 1)]
        """
        return [
            (col, row)
            for col in range(self.N)
            for row in range(self.N)
            if self.grid[row][col]
        ]

    def columns(self):
        """Gets a 2D list of the points in each column.

        A list of lists holding the coordinate tuples for points in each column. If there are no
        points in the column, then that list will be empty. The nth list in the 2D list contains all
        the points in the grid where x = n.

        Point (0, 0) is the bottom left corner.

        Returns:
            A 2D list.

            Example: A grid which looks like
                011
                001
                011
                returns the list [[], [(1, 0), (1, 2)], [(2, 0), (2, 1), (2, 2)]]
        """
        return [
            [(col, row) for row in range(self.N) if self.grid[row][col]]
            for col in range(self.N)
        ]

    def as_string(self):
        """Returns an ASCII string representation of the grid.

        A "1" indicates a point; "0" indicates the lack of a point. The grid is displayed with the
        origin (0, 0) at the bottom left corner, with the positive y direction going upwards and the
        positive x direction going right.

        Returns:
            A string representation of the grid.
        """
        queue = []
        for row in range(self.N):
            line = ""
            for col in range(self.N):
                line += "1" if self.grid[row][col] else "0"
            queue.insert(0, line)
        # construct in reverse order so positive y is up instead of down
        # while len(stack) > 0:
        #    print(stack.pop())
        return "\n".join(queue)

    def print(self):
        """Prints an ASCII representation of the grid."""
        print(self.as_string())


def construct_grid_from_model(N, solver):
    """Constructs a Grid object from the solver model.

    Args:
        N: the dimensions (number of rows and columns) of the grid.
        solver: the z3 solver.

    Returns:
        A grid if the constraints are satisfiable, or None if the constraints are unsatisfiable.
    """
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


def z3_nothree_solve(N):
    """Uses z3 smt to solve for a no-three-in-a-line grid.

    Uses a z3 solver to construct a grid under the constraint(s) that no three points are colinear.
    Because it is known for N <= 46 that there are solutions which place the maximum of 2*N points
    on the grid (https://oeis.org/A000769), this function is guaranteed to return a grid with 2*N
    points so long as N <= 46, and in fact assumes that 2*N points can indeed be placed such that no
    three points are colinear.

    There are two main sets of constraints: The first set trivially asserts that there must be 2*N
    unique points which fall within the bounds of the grid.

    The second set of constraints asserts that no three points are colinear by calculating the area
    formed by the triangles of every combination of points in the grid. Since three colinear points
    forms a degenerate triangle, the constraint asserts that all triangles formed by any combination
    of three points must have a non-zero area.

    Args:
        N: the dimensions (number of rows and columns) of the grid.

    Returns:
        A z3 solver populated with the constraints if it is satisfiable, or None if it is
        unsatisfiable.
    """

    solver = Solver()

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
    # so to assert that no three points are colinear, assert that the det of the matrix is not 0
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
        # calculate the determinant of the matrix above -- no need to halve the absolute value
        # since we are just checking that the result is not equal to 0
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
        return solver
    else:
        return None


def no_three_in_a_line(N):
    """Calls and times the z3 solver to construct a solution for N.

    Args:
        N: the dimensions (number of rows and columns) of the grid.

    Returns:
        A tuple of (float, Grid) containing the solution to the no-three-in-a-line problem, along
        with the time in seconds finding the solution.
        Or, if the solver is unable to find a solution, a tuple of (float, None) is returned.
    """
    time_start = perf_counter()
    solution = z3_nothree_solve(N)
    time_end = perf_counter()

    t = time_end - time_start
    return (t, solution)


def is_valid(grid):
    """Checks that no three points in the grid are colinear.

    This function checks the line equations given by every combination of points to ensure that no
    two equations are duplicated (i.e., for any two lines, they either differ in slope or offset).
    Since vertical lines have undefined slopes, they are handled separately: each column is simply
    checked to assert that no column contains more than two points.

    Args:
        grid: an N*N instance of a Grid.

    Returns:
        True if there are no three colinear points, or False if there are any three colinear points.
    """
    # make sure no more than 2 points are in each vertical column
    for column in grid.columns():
        if len(column) > 2:
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
            return False
        else:
            lines.add(line)

    return True


def naive(N):
    """Naively attempts to brute-force the no-three-in-a-line problem.

    Naively calculates the maximum number of pieces that can be placed on a board of size NxN
    such that no 3 pieces are colinear. This is O(2^N), since every possible placement (piece or
    no piece) is tested.

    This only serves as a reference to see how long this approach would take compared to
    using the smt solver.

    Args:
        N: the dimensions (number of rows and columns) of the grid.

    Returns:
        TODO
    """
    return False


def main(N):
    """Solves the no-three-in-a-line problem for 2 up to N and writes the results to solutions.txt.

    Args:
        N: the dimensions (number of rows and columns) of the grid.

    Returns:
        None

    Raises:
        TypeError: if N is not an integer
        ValueError: if N is not positive
    """
    if not isinstance(N, int):
        raise TypeError("N must be an integer")
    if N <= 0:
        raise ValueError("N must be positive")

    f = open("solutions.txt", "a")

    for n in range(2, N + 1):
        t, s = no_three_in_a_line(n)
        if s is None:
            f.write("No solution found for N=" + str(n) + "\n")
        else:
            grid = construct_grid_from_model(n, s)
            f.write(grid.as_string())
            f.write("\n")
        f.write("N=" + str(n) + ", t=" + str(t) + "s\n\n")
        f.flush()  # write solutions live

    f.close()


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3", sys.argv[0], "[N]")
        exit()

    main(int(sys.argv[1]))
