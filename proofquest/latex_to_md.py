"""Deterministic conversion of blueprint LaTeX fragments to game markdown.

The lean4game frontend renders markdown with KaTeX, so math mode is kept
(``\\[ \\]`` becomes ``$$ $$`` and ``\\( \\)`` becomes ``$ $``); only a small,
documented subset of text macros is translated.
"""

from __future__ import annotations

import re

_STRIP_MACROS = ("label", "lean", "uses")

_REF_MACROS = ("nameref", "Cref", "cref", "ref", "eqref")


def latex_to_markdown(tex: str, ref_titles: dict[str, str] | None = None) -> str:
    """Convert a LaTeX fragment to markdown, deterministically."""
    ref_titles = ref_titles or {}
    text = tex

    # Remove blueprint bookkeeping macros and \leanok.
    for macro in _STRIP_MACROS:
        text = re.sub(r"\\" + macro + r"\{[^{}]*\}", "", text)
    text = text.replace("\\leanok", "")

    # Display and inline math delimiters.
    text = re.sub(r"\\\[", "$$", text)
    text = re.sub(r"\\\]", "$$", text)
    text = re.sub(r"\\\(", "$", text)
    text = re.sub(r"\\\)", "$", text)

    # References: use the target's title when known, otherwise the label.
    def _ref(match: re.Match[str]) -> str:
        label = match.group(2)
        return "*" + ref_titles.get(label, label) + "*"

    text = re.sub(r"\\(" + "|".join(_REF_MACROS) + r")\{([^{}]*)\}", _ref, text)

    # Common text formatting macros.
    text = re.sub(r"\\(?:emph|textit)\{([^{}]*)\}", r"*\1*", text)
    text = re.sub(r"\\textbf\{([^{}]*)\}", r"**\1**", text)
    text = re.sub(r"\\texttt\{([^{}]*)\}", r"`\1`", text)

    # Unescape characters that need no escaping in markdown.
    text = re.sub(r"\\([%&#_])", r"\1", text)

    # Normalise whitespace: collapse runs of blank lines, trim lines.
    lines = [line.strip() for line in text.splitlines()]
    out: list[str] = []
    for line in lines:
        if line == "" and (not out or out[-1] == ""):
            continue
        out.append(line)
    while out and out[-1] == "":
        out.pop()
    return "\n".join(out)


def lean_string(text: str) -> str:
    """Escape a markdown string for embedding in a Lean string literal."""
    return text.replace("\\", "\\\\").replace('"', '\\"')


def lean_interp_string(text: str) -> str:
    """Escape for a Lean *interpolated* string (used by the `Hint` command).

    Interpolated strings treat ``{``/``}`` as interpolation delimiters. They are
    not directly escapable, so we emit them as Unicode hex escapes.
    """
    return (
        text.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("{", "\\u007b")
        .replace("}", "\\u007d")
    )
