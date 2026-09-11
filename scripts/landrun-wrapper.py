#!/usr/bin/env python3
"""Keep Comparator's command delimiter intact when invoking pinned Landrun."""

import os
from pathlib import Path
import sys

VALUE_OPTIONS = frozenset({
    "--log-level", "--ro", "--rox", "--rw", "--rwx", "--unix",
    "--bind-tcp", "--connect-tcp", "--env",
})
FLAG_OPTIONS = frozenset({
    "--best-effort", "--ignore-missing", "--log-disable-originating",
    "--log-enable-subprocesses", "--log-disable-subdomains",
    "--ldd", "-ldd", "--add-exec", "-add-exec",
})
GIT_ENVIRONMENT = (
    "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_NOSYSTEM=1", "GIT_TERMINAL_PROMPT=0",
)


def adapt(arguments):
    """Preserve every command argument and insert exactly one outer delimiter."""
    options = []
    index = 0
    while index < len(arguments):
        argument = arguments[index]
        if argument == "--":
            index += 1
            break
        if not argument.startswith("-"):
            break
        option, equal, value = argument.partition("=")
        if option in VALUE_OPTIONS:
            if equal:
                if not value:
                    raise ValueError(f"missing value for {option}")
                options.append(argument)
                index += 1
            else:
                if index + 1 >= len(arguments) or arguments[index + 1] == "--":
                    raise ValueError(f"missing value for {option}")
                options.extend(arguments[index:index + 2])
                index += 2
        elif argument in FLAG_OPTIONS:
            options.append(argument)
            index += 1
        else:
            raise ValueError(f"unsupported Landrun option: {option}")
    command = arguments[index:]
    if not command:
        raise ValueError("missing sandboxed command")
    isolated_git = [item for setting in GIT_ENVIRONMENT for item in ("--env", setting)]
    return [*options, *isolated_git, "--", *command]


def main():
    try:
        binary = Path(os.environ["PALOMAR_LANDRUN_REAL"]).resolve(strict=True)
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise ValueError("PALOMAR_LANDRUN_REAL must name an executable file")
        arguments = adapt(sys.argv[1:])
        os.execv(str(binary), [str(binary), *arguments])
    except (KeyError, OSError, ValueError) as error:
        print(f"Landrun adapter: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
