"""Pinning of generated games to lean4game release tags.

lean4game publishes release tags of the form ``v4.X.0`` (see the tags of
https://github.com/leanprover-community/lean4game). Generated games are built
against such a tag, and the local server artifacts must use the same one.
"""

from __future__ import annotations

import re

_RELEASES = [
    (4, 1),
    (4, 2),
    (4, 3),
    (4, 4),
    (4, 5),
    (4, 6),
    (4, 7),
    (4, 21),
    (4, 22),
    (4, 23),
    (4, 28),
    (4, 29),
    (4, 31),
]
LATEST_GAME_TOOLCHAIN = "leanprover/lean4:v4.31.0"
_VERSION_RE = re.compile(r"v?(\d+)\.(\d+)\.(\d+)")


def game_toolchain(project_toolchain: str | None) -> tuple[str, str | None]:
    """Pick the generated game's toolchain.

    The game is built against a lean4game release tag `v4.X.0`, so a project on
    a newer Lean release (e.g. `v4.32.2`) must have its *game* downgraded to the
    newest compatible tag. Returns ``(toolchain, warning)``.
    """
    if project_toolchain is None:
        return LATEST_GAME_TOOLCHAIN, None
    version = _VERSION_RE.search(project_toolchain)
    if version is None or int(version.group(1)) != 4:
        return LATEST_GAME_TOOLCHAIN, (
            f"project toolchain {project_toolchain!r} unrecognized; "
            f"generated game uses {LATEST_GAME_TOOLCHAIN}"
        )
    major, minor, patch = (int(g) for g in version.groups())
    target = next(
        (
            (rm, rn)
            for rm, rn in reversed(_RELEASES)
            if rm == major and rn <= minor
        ),
        None,
    )
    toolchain = (
        f"leanprover/lean4:v{target[0]}.{target[1]}.0"
        if target is not None
        else LATEST_GAME_TOOLCHAIN
    )
    if target == (major, minor) and patch == 0:
        return toolchain, None
    return toolchain, (
        f"project toolchain {project_toolchain!r} has no matching lean4game release; "
        f"generated game uses {toolchain}"
    )
