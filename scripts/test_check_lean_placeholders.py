#!/usr/bin/env python3
"""Regression tests for the lightweight Lean source stripper."""

from __future__ import annotations

import unittest

from check_lean_placeholders import TOKEN_RE, strip_comments_and_strings


class StripCommentsAndStringsTests(unittest.TestCase):
    def assert_placeholder_detected(self, source: str) -> None:
        self.assertIsNotNone(TOKEN_RE.search(strip_comments_and_strings(source)))

    def assert_no_placeholder_detected(self, source: str) -> None:
        self.assertIsNone(TOKEN_RE.search(strip_comments_and_strings(source)))

    def test_placeholder_after_primed_identifier_is_visible(self) -> None:
        self.assert_placeholder_detected("def pos' := 1\nexample : True := by sorry\n")

    def test_placeholder_after_double_primed_identifier_is_visible(self) -> None:
        self.assert_placeholder_detected("def pos'' := 1\nexample : True := by sorry\n")

    def test_comments_and_strings_are_ignored(self) -> None:
        self.assert_no_placeholder_detected(
            '-- sorry\n/- admit -/\ndef message := "sorry and admit"\n'
        )

    def test_character_literal_does_not_hide_following_placeholder(self) -> None:
        self.assert_placeholder_detected(
            "def apostrophe : Char := '\\''\nexample : True := by sorry\n"
        )


if __name__ == "__main__":
    unittest.main()
