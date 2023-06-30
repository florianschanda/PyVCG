import unittest

from pyvcg import graph


class GraphBasicTests(unittest.TestCase):
    def setUp(self):
        self.g = graph.DAG()

    def testSimple01(self):
        n1 = graph.Node(self.g)
        n2 = graph.Node(self.g)
        n3 = graph.Node(self.g)

        n1.add_edge_to(n2)
        self.assertTrue(self.g.path_exists(n1, n1))
        self.assertTrue(self.g.path_exists(n1, n2))
        self.assertFalse(self.g.path_exists(n2, n1))
        self.assertFalse(self.g.path_exists(n2, n3))

        n2.add_edge_to(n3)
        self.assertTrue(self.g.path_exists(n1, n3))

        with self.assertRaises(AssertionError):
            n3.add_edge_to(n1)

        with self.assertRaises(AssertionError):
            n1.add_edge_to(n1)

    def testSimple02(self):
        # n0 (start)
        # n1
        # n2 --- n3
        #  |  n4     n5
        #  | /      / \
        # n6 ------/   n7
        n0 = graph.Start(self.g)
        n1 = graph.Assumption(self.g)
        n2 = graph.Assumption(self.g)
        n3 = graph.Assumption(self.g)
        n4 = graph.Assumption(self.g)
        n5 = graph.Assumption(self.g)
        n6 = graph.Check(self.g)
        n7 = graph.Check(self.g)
        n0.add_edge_to(n1)
        n1.add_edge_to(n2)
        n2.add_edge_to(n3)
        n2.add_edge_to(n6)
        n3.add_edge_to(n4)
        n3.add_edge_to(n5)
        n4.add_edge_to(n6)
        n5.add_edge_to(n6)
        n5.add_edge_to(n7)

        self.assertTrue(self.g.path_exists(n0, n6))

        required_paths = [
            [0, 1, 2, 6],
            [0, 1, 2, 3, 4, 6],
            [0, 1, 2, 3, 5, 6],
            [0, 1, 2, 3, 5, 7]
        ]

        for path in self.g.all_paths_to_checks():
            self.assertTrue(path in required_paths)
            del required_paths[required_paths.index(path)]

        self.assertEqual(len(required_paths), 0)
