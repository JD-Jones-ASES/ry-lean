#!/usr/bin/env python3
"""Regression checks for the exact argv passed to the sandbox executable."""

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
import unittest

source = Path(__file__).with_name("landrun-wrapper.py")
spec = importlib.util.spec_from_file_location("landrun_wrapper", source)
wrapper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wrapper)


class LandrunArguments(unittest.TestCase):
    def command(self, arguments):
        result = wrapper.adapt(arguments)
        return result[result.index("--") + 1:]

    def test_exporter_delimiter_is_preserved(self):
        command = ["/tmp/exporter with spaces", "--", "Challenge", "a b"]
        self.assertEqual(self.command(["--ro", "/tmp/source", *command]), command)
        self.assertEqual(self.command(["--ro", "/tmp/source", "--", *command]), command)

    def test_options_and_git_isolation(self):
        result = wrapper.adapt(["--ro=/tmp/a b", "-ldd", "lake", "build"])
        self.assertEqual(result[:2], ["--ro=/tmp/a b", "-ldd"])
        for setting in wrapper.GIT_ENVIRONMENT:
            self.assertIn(setting, result[:result.index("--")])
        self.assertEqual(self.command(["lake", "build"]), ["lake", "build"])

    def test_invalid_options_fail(self):
        for arguments in (["--ro"], ["--ro="], ["--ro", "--"], [], ["--"],
                          ["--unrestricted-filesystem", "lake"],
                          ["-unrestricted-network", "lake"], ["--unknown", "lake"]):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                wrapper.adapt(arguments)

    def test_executable_receives_exact_arguments_and_exit_status(self):
        with tempfile.TemporaryDirectory() as temporary:
            fake = Path(temporary) / "fake landrun"
            fake.write_text("#!/usr/bin/env python3\nimport json, sys\n"
                            "print(json.dumps(sys.argv[1:]))\nraise SystemExit(7)\n")
            fake.chmod(0o700)
            arguments = ["--ro", "/tmp/source with spaces", "--", "lake", "--", "arg"]
            environment = dict(os.environ, PALOMAR_LANDRUN_REAL=str(fake))
            result = subprocess.run([sys.executable, str(source), *arguments],
                                    env=environment, text=True, capture_output=True)
            self.assertEqual(result.returncode, 7, result.stderr)
            self.assertEqual(json.loads(result.stdout), wrapper.adapt(arguments))

    def test_command_options_are_not_reparsed(self):
        command = ["lake", "--unknown-to-landrun", "--", "--env=literal"]
        self.assertEqual(self.command(command), command)


if __name__ == "__main__":
    unittest.main()
