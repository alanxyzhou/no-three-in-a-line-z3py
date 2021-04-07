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
        """Returns a list of (x,y) tuples representing the coordinates of
        filled points on the grid
        """
        return [
            (row, col)
            for row in range(self.N)
            for col in range(self.N)
            if self.grid[row][col]
        ]

    def print(self):
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
        print("solver returned unsat")
        return None


def create_real_assertions(N):
    """
    Creates assertions that for 2*N points, no two points share an identical line equation.
    This accounts for Case 2 in the overall assertions and must be OR'd with Case 1 and Case 3.
    """
    real_assertions = []
    point_tuples = []
    # create (2N choose 2) pairs of slopes between points i and j
    for i in range(2 * N - 1):
        for j in range(i + 1, 2 * N):
            point_tuples.append((i, j))
    # create assertions that for each unique combination of lines created by two points,
    # they are both real and differ in either slope or offset
    for point_pair in combinations(point_tuples, 2):
        ij = point_pair[0]
        uv = point_pair[1]

        m_ij = Int("m_{0}_{1}".format(ij[0], ij[1]))
        b_ij = Int("b_{0}_{1}".format(ij[0], ij[1]))
        x_i = Int("x_{0}".format(ij[0]))
        x_j = Int("x_{0}".format(ij[1]))

        m_uv = Int("m_{0}_{1}".format(uv[0], uv[1]))
        b_uv = Int("b_{0}_{1}".format(uv[0], uv[1]))
        x_u = Int("x_{0}".format(uv[0]))
        x_v = Int("x_{0}".format(uv[1]))

        real_assertions.append(
            And(
                And(x_i != x_j, x_u != x_v),  # both slopes are not infinite
                Or(m_ij != m_uv, b_ij != b_uv),  # both lines differ in slope or offset
            )
        )

    real_assertions_conjunct = And(real_assertions)

    print(real_assertions_conjunct)
    return real_assertions_conjunct


def create_one_real_one_inf_assertions(N):
    """
    Creates assertions that for 2*N points, for any combination of slopes created by the two points,
    where one slope is real and the other is infinite, the lines are distinct so they must be allowed.
    This accounts for Case 3 in the overall assertions and must be OR'd with Case 1 and Case 2.
    """
    one_real_one_inf_assertions = []
    point_tuples = []
    # create (2N choose 2) pairs of slopes between points i and j
    for i in range(2 * N - 1):
        for j in range(i + 1, 2 * N):
            point_tuples.append((i, j))
    # create assertions that for each unique combination of lines created by two points,
    # one is real and the other is infinite.
    for point_pair in combinations(point_tuples, 2):
        ij = point_pair[0]
        uv = point_pair[1]

        m_ij = Int("m_{0}_{1}".format(ij[0], ij[1]))
        b_ij = Int("b_{0}_{1}".format(ij[0], ij[1]))
        x_i = Int("x_{0}".format(ij[0]))
        x_j = Int("x_{0}".format(ij[1]))

        m_uv = Int("m_{0}_{1}".format(uv[0], uv[1]))
        b_uv = Int("b_{0}_{1}".format(uv[0], uv[1]))
        x_u = Int("x_{0}".format(uv[0]))
        x_v = Int("x_{0}".format(uv[1]))

        one_real_one_inf_assertions.append(
            Or(And(x_i == x_j, x_u != x_v), And(x_i != x_j, x_u == x_v))
        )

    one_real_one_inf_conjunct = And(one_real_one_inf_assertions)
    return one_real_one_inf_conjunct


def three_solve(N):
    """Uses a z3 solver to check that no three points in the grid are colinear."""
    # y = mx + b
    solver = Solver()

    # strategy:
    # add 2n points
    # for each point, constraint is that it must form a unique line equation with every other point

    # look for a solution with 2*N points (maximum number per pigeonhole principle)

    # add 2N unique points to the model
    points = []
    for i in range(2 * N):
        x_i = Int("x_{0}".format(i))
        y_i = Int("y_{0}".format(i))
        tup = (x_i, y_i)
        points.append(tup)
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

    # add (2*N choose 2) lines to the model (between every combination of points)
    for i in range((2 * N) - 1):
        for j in range(i + 1, (2 * N)):
            # y = mx + b
            # b = y - mx
            x_i = Int("x_{0}".format(i))
            y_i = Int("y_{0}".format(i))
            x_j = Int("x_{0}".format(j))
            y_j = Int("y_{0}".format(j))
            m_ij = Int("m_{0}_{1}".format(i, j))
            b_ij = Int("b_{0}_{1}".format(i, j))
            solver.add(m_ij == ((y_j - y_i) / (x_j - x_i)))
            solver.add(b_ij == (y_i - (m_ij * x_i)))

    # assert that the line formed by every point is unique
    """
    In z3, dividing by 0 returns 0. This is a big problem because a 0 slope is indistinguishable from an infinite slope. 

    Therefore, when comparing slopes for uniqueness, we must split this into multiple conditions, and we want ANY of these three to pass:
    1. This slope is infinite (x_i == x_j):
        - check that there are no more than 2 points with this x coord
            This can be done by transposing the grid and applying the uniqueness rule, ignoring vertical lines (which were horizontal)
    2. This slope is real, and the other slope is real (x_i != x_j and x_u != x_v):
        - check that this line is not an exact match with the other line
            i.e., m_ij != m_uv || b_ij != b_uv
    3. This slope is real, and the other slope is infinite (x_i != x_j and x_u == x_v) or (x_i == x_j and x_u != x_v):
        - the slopes are unique by definition. No additional work to be done
    """
    distinct_lines_assertations = []
    distinct_lines_assertations.append(create_real_assertions(N))
    distinct_lines_assertations.append(create_one_real_one_inf_assertions(N))
    """
    for i in range((2 * N) - 1):
        for j in range(i + 1, (2 * N)):
            any_of_three_cases_assertations = []

            # _ij is "this" line
            m_ij = Int("m_{0}{1}".format(i, j))
            b_ij = Int("b_{0}{1}".format(i, j))
            # x points for "this" line
            x_i = Int("x_{0}".format(i))
            x_j = Int("x_{0}".format(j))

            # Case 1: Assert that if this slope is infinite, there are no more than 2 points on this x axis
            # TODO 
            # any_of_three_cases_assertations.append(...)

            # compare this line and slope against every other line and slope
            for u in range((2 * N) - 1):
                for v in range(i + 1, (2 * N)):
                    if i != u or j != v:
                        # _uv is "other" line, compare against "this" line _ij
                        m_uv = Int("m_{0}{1}".format(u, v))
                        b_uv = Int("b_{0}{1}".format(u, v))
                        # x points for "other" line
                        x_u = Int("x_{0}".format(u))
                        x_v = Int("x_{0}".format(v))

                        # Case 2
                        both_slopes_real_assertations = And(
                            And(x_i != x_j, x_u != x_v), Or(m_ij != m_uv, b_ij != b_uv)
                        )
                        any_of_three_cases_assertations.append(
                            both_slopes_real_assertations
                        )
                        # Case 3
                        one_slope_real_other_infinite = Or(
                            And(x_i != x_j, x_u == x_v), And(x_i == x_j, x_u != x_v)
                        )
                        any_of_three_cases_assertations.append(
                            one_slope_real_other_infinite
                        )

            distinct_lines_assertations.append(Or(any_of_three_cases_assertations))
    """

    solver.add(Or(distinct_lines_assertations))

    # test
    print("----------------------------------------")
    print(solver.assertions())
    if solver.check() == sat:
        print(solver.model())
    else:
        print("unsat")
    g = construct_grid_from_model(N, solver)
    g.print()

    return False


def is_valid(grid):
    lines = {None}
    # every 2 points should form a unique line equation
    for points_tuple in combinations(grid.points(), 2):
        p1 = points_tuple[0]
        p2 = points_tuple[1]

        # y = mx + b
        delta_y = p2[1] - p1[1]
        delta_x = p2[0] - p1[0]

        if delta_x == 0:
            m = math.inf
        else:
            m = delta_y / delta_x

        b = p1[1] - (m * p1[0])

        line = (m, b)
        if line in lines:
            print("line", line, "duplicated: invalid grid")  # debug
            return False
        else:
            print("line", line, "ok")  # debug
            lines.add(line)

    return True


def naive(N):
    """Naively calculates the maximum number of pieces that can be placed on a board of size NxN
    such that no 3 pieces are colinear. This is O(2^N), since every possible placement (piece or
    no piece) is tested.

    Returns a list of boards
    """
    return False


def main(N):
    """
    # test1 = Grid(3, "100110010")
    test1 = Grid(3, "100110011")
    test1.print()

    for points_tuple in combinations(test1.points(), 2):
        print(points_tuple)

    print("is valid:", is_valid(test1))
    """
    three_solve(N)
    # create_real_assertions(N)


if __name__ == "__main__":
    main(int(sys.argv[1]))
