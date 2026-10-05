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


@dataclass(frozen=True)
class LeanNotation:
    module: str
    line: int
    namespace: str
    pattern: str
    target: str
    arguments: tuple[str, ...]
    expression: str | None = None
    variables: tuple[str, ...] = ()
    opens: tuple[str, ...] = ()


@dataclass(frozen=True)
class LeanContextCommand:
    module: str
    source_path: str
    line: int
    end_line: int
    namespace: str
    scope: tuple[str, ...]
    kind: str
    source_text: str
    exported: bool
    supported: bool
    targets: tuple[str, ...] = ()
    instance_action: str | None = None
    priority: int | None = None
    variables: tuple[str, ...] = ()
    opens: tuple[str, ...] = ()


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
    module: str = ""
    line: int = 0
    local_syntax: list[str] = field(default_factory=list)
    notations: list[LeanNotation] = field(default_factory=list)
    source_path: str = ""
    modifiers: tuple[str, ...] = ()
    scope: tuple[str, ...] = ()
    context: tuple[LeanContextCommand, ...] = ()
    instances: list[LeanDecl] = field(default_factory=list)
    context_namespace: str | None = None
    noncomputable_section: bool = False
    external_namespaces: frozenset[str] = frozenset()

    @property
    def is_definition(self) -> bool:
        return self.keyword in ("def", "abbrev", "instance", "structure", "class")


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
class DefsStage:
    """Auxiliary declarations that become importable only after some levels.

    ``index`` counts the levels (in global emission order) that must precede
    the stage: ``0`` is the preamble ``Game/Generated/Defs.lean`` (imported
    by ``Game.Metadata`` before any level), while ``index >= 1`` renders to
    ``Game/Generated/DefsAfter<index:03d>.lean``, a module importing the
    level at that global position — and with it every earlier level and
    stage — so the blueprint theorems the staged declarations rely on are
    already in scope.
    """

    index: int
    level: Level | None = None
    definitions: list[tuple[LeanDecl, BlueprintNode | None]] = field(
        default_factory=list
    )
    imports: list[int] = field(default_factory=list)

    @property
    def module_stem(self) -> str:
        return "Defs" if self.index == 0 else f"DefsAfter{self.index:03d}"

    @property
    def module(self) -> str:
        return f"Game.Generated.{self.module_stem}"


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
    stages: list[DefsStage] = field(default_factory=list)
    world_dependencies: list[tuple[str, str]] = field(default_factory=list)
    project_scopes: frozenset[str] = frozenset()
    decls: dict[str, LeanDecl] = field(default_factory=dict)
