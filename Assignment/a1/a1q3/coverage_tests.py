import unittest

from . import token_with_escape 


class CoverageTests(unittest.TestCase):
    def test_1(self):
        """Node Coverage but not Edge Coverage"""
        # YOUR CODE HERE
        # Path : [8,11,12,13,14,11,12,20,21,11,23]
        output = token_with_escape('^a')
        expected = ['a']
        self.assertListEqual(output, expected)
        # Path : [8,11,12,13,15,16,11,23]
        expected = ['','']
        output = token_with_escape('|')
        self.assertListEqual(output, expected)
        # Path : [8,11,12,13,15,19,11,23]
        expected = ['a']
        output = token_with_escape('a')
        self.assertListEqual(output, expected)
        pass

    def test_2(self):
        """Edge Coverage but not Edge Pair Coverage"""
        # YOUR CODE HERE
        # Path : [8,11,12,13,14,11,12,20,21,11,23]
        output = token_with_escape('^a')
        expected = ['a']
        self.assertListEqual(output, expected)
        # Path : [8,11,12,13,15,19,11,23]
        output = token_with_escape('a')
        expected = ['a']
        self.assertListEqual(output, expected)
        # Path : [8,11,12,13,15,16,11,23]
        output = token_with_escape('|')
        expected = ['','']
        self.assertListEqual(output, expected)

        pass

    def test_3(self):
        """Edge Pair Coverage but not Prime Path Coverage"""
        # YOUR CODE HERE
        # Path : [8,11,12,13,14,11,12,20,21,11,12,13,14,11,23]
        output = token_with_escape('^a^')
        expected = ['a']
        self.assertListEqual(output, expected)
        # Path : [8,11,12,13,15,19,11,12,13,15,19,11,23]
        output = token_with_escape('||')
        expected = ['','','']
        self.assertListEqual(output, expected)
        # Path : [8,11,12,13,15,16,11,12,13,15,16,11,23]
        output = token_with_escape('aa')
        expected = ['aa']
        self.assertListEqual(output, expected)
        # Path : [8,11,12,13,14,11,12,20,21,11,23]
        output = token_with_escape('^a')
        expected = ['a']
        self.assertListEqual(output, expected)
        # Path : [8,11,23]
        output = token_with_escape('')
        expected = ['']
        self.assertListEqual(output, expected)

        pass
