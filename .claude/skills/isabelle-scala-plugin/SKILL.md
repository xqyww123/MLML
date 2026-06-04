---
name: isabelle-scala-plugin
description: How to write Isabelle/Scala plugins (Scala.Fun) that ML can call via PIDE protocol
---

# Isabelle/Scala Plugins (Scala.Fun)

Isabelle's `Scala.Fun` mechanism lets ML code call Scala/JVM functions via the PIDE protocol. Use this when you need JVM capabilities from ML: file I/O, accessing PIDE session/document state, network, Java libraries, etc.

**Working example:** `contrib/Semantic_Embedding/src/scala/pide_state.scala` + `contrib/Semantic_Embedding/Tools/pide_state.ML`

**Framework source:** `contrib/Isabelle2024/src/Pure/System/scala.scala`

## 1. Component Setup

A Scala plugin requires a registered Isabelle **component** with these files:

### `etc/settings`
```bash
# -*- shell-script -*- :mode=shellscript:
MY_COMPONENT_HOME="$COMPONENT"
classpath "$MY_COMPONENT_HOME/lib/my_plugin.jar"
```

The `classpath` call is sufficient for both class loading AND service discovery (the jar's `META-INF/isabelle/services` is auto-scanned).

**WARNING:** Do NOT add `isabelle_scala_service` in settings — it causes jEdit startup crash (code 127).

### `etc/build.props`
```properties
title = Isabelle/Scala/My_Plugin
module = lib/my_plugin.jar
no_build = true
requirements = \
  env:ISABELLE_SCALA_JAR
sources = \
  src/scala/my_plugin.scala
services = \
  my.package.My_Functions
```

**CRITICAL:** `no_build = true` is mandatory. Without it, jEdit crashes at startup with return code 127 (COMMAND NOT FOUND). You must manually run `isabelle scala_build` after temporarily removing this flag.

### Component registration
```bash
isabelle components -u /path/to/my/component
```

## 2. Scala Side

### Subclass choices

| Base class | Use when | ML calls with |
|---|---|---|
| `Scala.Fun` + override `invoke` | Need `Session` object (document state, etc.) | `Scala.function` / `Scala.function1` |
| `Scala.Fun_String` | Simple string→string, no Session needed | `Scala.function1` |
| `Scala.Fun_Bytes` | Binary data | `Scala.function1_bytes` |

### Template: Fun with Session access

```scala
package isabelle.my_package

import isabelle._

object My_Function extends Scala.Fun("my_package.my_function", thread = true)
  with Scala.Single_Fun
{
  val here = Scala_Project.here

  override def invoke(session: Session, args: List[Bytes]): List[Bytes] = {
    val input = args.head.text  // single string argument from ML

    // ... do work ...

    val body = XML.Encode.list(XML.Encode.string)(result_list)
    List(Bytes(YXML.string_of_body(body)))
  }
}

class My_Functions extends Scala.Functions(My_Function)
```

Key points:
- `thread = true`: runs in a separate thread (required for session state access)
- `Scala.Single_Fun`: function takes/returns a single value (wrapped in `List`)
- `val here = Scala_Project.here`: required for error position reporting

### Template: Fun_String (simple)

```scala
object Echo extends Scala.Fun_String("my_package.echo") {
  val here = Scala_Project.here
  def apply(arg: String): String = arg.toUpperCase
}
```

### Service class

Register all functions in one service class:

```scala
class My_Functions extends Scala.Functions(Function1, Function2, Function3)
```

## 3. Accessing PIDE Document State

### Document.Version (all nodes/commands, no state info)
```scala
val version = session.get_state().recent_finished.version.get_finished
```

### Document.Snapshot (full state, can resolve positions)
```scala
val snapshot = session.get_state().snapshot()
```

### Key APIs on Version/Node

```scala
// iterate all theory nodes
for ((name, node) <- version.nodes.iterator if name.is_theory) {
  val file_path: String = name.node        // e.g., "/path/to/Foo.thy"
  val source: String = node.source          // full source text

  // iterate commands
  for (command <- node.commands.iterator) {
    val id: Long = command.id
    val cmd_source: String = command.source
    val line: Option[Int] = node.command_start_line(command)  // 1-based
  }
}

// resolve command ID + offset to file position (needs Snapshot)
snapshot.find_command_position(id, offset)  // => Option[Line.Node_Position]
// Line.Node_Position has: .name (file), .line1 (1-based line), .column1 (1-based column)
```

## 4. ML Side

### Calling Scala functions

```sml
(* string -> string *)
val result = Scala.function1 "my_package.my_function" input_string;

(* string list -> string list *)
val results = Scala.function "my_package.my_function" input_strings;

(* Bytes.T -> Bytes.T *)
val result = Scala.function1_bytes "my_package.my_function" input_bytes;
```

### Loading in a theory

```isabelle
theory My_Theory imports Main
begin
ML_file \<open>Tools/my_tool.ML\<close>
end
```

## 5. XML Encode/Decode Cheat Sheet

Data interchange between ML and Scala uses YXML-encoded XML trees.

### Encoding (Scala → YXML string)

```scala
// primitives
XML.Encode.string : T[String]
XML.Encode.int    : T[Int]
XML.Encode.long   : T[Long]
XML.Encode.bool   : T[Boolean]

// combinators
XML.Encode.pair(f, g)    : T[(A, B)]
XML.Encode.triple(f,g,h) : T[(A, B, C)]
XML.Encode.list(f)       : T[List[A]]
XML.Encode.option(f)     : T[Option[A]]

// wrap to string
val yxml_string = YXML.string_of_body(XML.Encode.list(XML.Encode.string)(my_list))
```

### Decoding (YXML string → ML)

```sml
(* primitives *)
XML.Decode.string : body -> string
XML.Decode.int    : body -> int    (* arbitrary precision, can decode Scala long *)

(* combinators *)
XML.Decode.pair f g      : body -> 'a * 'b
XML.Decode.triple f g h  : body -> 'a * 'b * 'c
XML.Decode.list f        : body -> 'a list
XML.Decode.option f      : body -> 'a option

(* parse from string *)
val decoded = YXML.parse_body yxml_string |> XML.Decode.list XML.Decode.string;
```

### ML encoding (ML → YXML string → Scala)

```sml
val body = XML.Encode.list (XML.Encode.pair XML.Encode.int XML.Encode.int) pairs;
val yxml_string = YXML.string_of_body body;
```

Scala decoding:
```scala
val pairs = XML.Decode.list(XML.Decode.pair(XML.Decode.int, XML.Decode.int))(
  YXML.parse_body(input_string))
```

## 6. Build & Deploy Workflow

### Building the jar

```bash
# 1. Temporarily enable building
sed -i '/^no_build/d' contrib/My_Component/etc/build.props

# 2. Build
isabelle scala_build

# 3. Restore no_build (CRITICAL for jEdit)
sed -i '/^module = lib/a no_build = true' contrib/My_Component/etc/build.props
```

### When to rebuild/restart

| Changed | Action needed |
|---|---|
| `.scala` file | Rebuild jar + restart jEdit |
| `.ML` file only | Reload theory in jEdit (no rebuild) |
| `etc/settings` | Restart jEdit |
| `etc/build.props` | Rebuild jar + restart jEdit |

### No output from `isabelle scala_build`?

This means the jar is already up-to-date (sources unchanged since last build). Verify with `ls lib/*.jar`.

## 7. Gotchas & Lessons Learned

1. **`no_build = true` is mandatory** in `etc/build.props`. Without it, jEdit startup crashes with `Return code: 127 (COMMAND NOT FOUND)`.

2. **Do NOT use `isabelle_scala_service`** in `etc/settings`. It also causes the 127 crash. The `classpath` call alone is sufficient — services are discovered from the jar's `META-INF/isabelle/services`.

3. **Position.T has no column field.** It stores: `line`, `offset` (symbol offset), `end_offset`, `label`, `file`, `id`. Construct with `Position.make0 line offset end_offset label file id` or helpers like `Position.line_file line file`.

4. **`find_command_position` returns 0-based positions.** Use `.line1` and `.column1` for 1-based values matching Isabelle convention.

5. **ML `int` is arbitrary precision** (Poly/ML), so `XML.Decode.int` on the ML side can decode values encoded with `XML.Encode.long` on the Scala side.

6. **`recent_finished` vs `snapshot()`**: Use `recent_finished.version.get_finished` for read-only access to the document version. Use `snapshot()` when you need to resolve positions or access command state.

## 8. PIDE Document Model Reference

### Key types (`contrib/Isabelle2024/src/Pure/PIDE/document.scala`)

- **`Document.Version`** — immutable snapshot of all theory nodes
  - `.nodes: Nodes` — graph of `(Node.Name, Node)` pairs
- **`Document.Node`** — a theory file's content
  - `.source: String` — full source text
  - `.commands: Linear_Set[Command]` — all commands in order
  - `.command_start_line(cmd): Option[Int]` — 1-based line number
- **`Document.Node.Name`** — theory file identity
  - `.node: String` — file path
  - `.theory: String` — theory name
  - `.is_theory: Boolean`
- **`Command`** — a single command (e.g., one `lemma`, one `definition`)
  - `.id: Long` — unique command ID
  - `.source: String` — command source text

### Session export database

Session databases at `~/.isabelle/Isabelle2024/heaps/<ML_ID>/log/<session>.db` contain persisted PIDE markup including entity references for go-to-definition. See `contrib/Semantic_Embedding/doc/goto_definition.md` for full details.
