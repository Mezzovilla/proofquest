"""Data model shared between the parsing and generation stages."""

from __future__ import annotations

from dataclasses import dataclass, field

THEOREM_KINDS = ("lemma", "theorem", "proposition", "corollary")
DEFINITION_KINDS = ("definition",)
ENV_KINDS = DEFINITION_KINDS + THEOREM_KINDS


@dataclass
class BlueprintNode:
    """One theorem-like environment extracted from the blueprint LaTeX."""

    kind: str
    label: str
    lean_names: list[str]
    title: str | None
    statement_tex: str
    proof_tex: str | None
    uses: list[str]
    leanok: bool
    chapter: str
    section: str | None
    order: int

    @property
    def is_theorem(self) -> bool:
        return self.kind in THEOREM_KINDS


@dataclass
class Blueprint:
    nodes: list[BlueprintNode]
    chapters: list[str]
    chapter_intros: dict[str, str] = field(default_factory=dict)

    def by_label(self) -> dict[str, BlueprintNode]:
        return {n.label: n for n in self.nodes}


@dataclass
class LeanDecl:
    """One declaration extracted from the Lean sources of the input project."""

    keyword: str  # def / theorem / lemma / abbrev / instance
    name: str  # short name as written in the source
    full_name: str  # namespace-qualified name
    namespace: str  # dot-joined namespace ("" for root)
    signature: str  # binders + goal, i.e. everything between name and `:=`
    proof: str | None  # text after `:=` (None for defs)
    source_text: str  # full declaration, verbatim
    variables: list[str] = field(default_factory=list)  # active `variable` lines
    imports: list[str] = field(default_factory=list)  # external Mathlib imports needed
    opens: list[str] = field(default_factory=list)  # active `open` statements

    @property
    def is_definition(self) -> bool:
        return self.keyword in ("def", "abbrev", "instance")


@dataclass
class Level:
    index: int  # 1-based within its world
    world_id: str
    file_stem: str  # e.g. "L01_lemma1"
    title: str
    intro_md: str
    hint_md: str | None
    decl: LeanDecl
    node: BlueprintNode
    new_definitions: list[LeanDecl] = field(default_factory=list)
    new_tactics: list[str] = field(default_factory=list)
    new_theorems: list[str] = field(default_factory=list)


@dataclass
class World:
    world_id: str
    title: str
    intro_md: str
    levels: list[Level] = field(default_factory=list)


@dataclass
class Game:
    title: str
    intro_md: str
    languages: str
    worlds: list[World]
    definitions: list[tuple[LeanDecl, BlueprintNode | None]]
    tactics: list[str]  # all tactics used, in order of first appearance
    theorems: list[str]  # all external theorems referenced, in order of first appearance
    toolchain: str
