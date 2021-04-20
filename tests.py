from ntial import *
import unittest


class TestGridMethods(unittest.TestCase):
    def test_empty_grids(self):
        for i in range(2, 50):
            g = Grid(i, "0" * i ** 2)
            s = g.as_string()
            e = ("0" * i + "\n") * i
            self.assertEqual(s, e[:-1])

    def test_grid_as_string_2(self):
        g = Grid(2, "1001")
        e = "01\n10"
        self.assertEqual(g.as_string(), e)

    def test_grid_as_string_3(self):
        g = Grid(3, "000110111")
        e = "111\n110\n000"
        self.assertEqual(g.as_string(), e)

    def test_grid_small_N_throws(self):
        try:
            g = Grid(0, "")
            self.assertTrue(False)
        except ValueError:
            self.assertTrue(True)

    def test_grid_negative_N_throws(self):
        try:
            g = Grid(-1, "")
            self.assertTrue(False)
        except ValueError:
            self.assertTrue(True)

    def test_grid_incomplete_instance_throws(self):
        try:
            g = Grid(3, "00011011")
            self.assertTrue(False)
        except ValueError:
            self.assertTrue(True)

    def test_grid_points(self):
        g = Grid(3, "100010001")
        points = [(0, 0), (1, 1), (2, 2)]
        self.assertEqual(g.points(), points)

    def test_grid_points_empty(self):
        g = Grid(3, "000000000")
        self.assertEqual(g.points(), [])

    def test_grid_columns(self):
        g = Grid(4, "0111000101010111")
        columns = [
            [],
            [(1, 0), (1, 2), (1, 3)],
            [(2, 0), (2, 3)],
            [(3, 0), (3, 1), (3, 2), (3, 3)],
        ]
        self.assertEqual(g.columns(), columns)

    def test_grid_columns_empty(self):
        g = Grid(4, "0000000000000000")
        columns = [[], [], [], []]
        self.assertEqual(g.columns(), columns)


class TestIsValid(unittest.TestCase):
    def test_valid_empty(self):
        for i in range(2, 50):
            g = Grid(i, "0" * i ** 2)
            self.assertTrue(is_valid(g))

    def test_valid_4x4(self):
        g = Grid(4, "1010101001010101")
        self.assertTrue(is_valid(g))

    def test_invalid_vertical_3x3(self):
        g = Grid(3, "100100100")
        self.assertFalse(is_valid(g))

    def test_invalid_horizontal_3x3(self):
        g = Grid(3, "000111000")
        self.assertFalse(is_valid(g))

    def test_invalid_diagonal_pos_3x3(self):
        g = Grid(3, "100010001")
        self.assertFalse(is_valid(g))

    def test_invalid_diagonal_neg_3x3(self):
        g = Grid(3, "001010100")
        self.assertFalse(is_valid(g))


# is_valid tests ===============================================================


# Solver validity tests ========================================================


################################################################################

if __name__ == "__main__":
    unittest.main()