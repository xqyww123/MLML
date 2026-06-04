---
name: isabelle-rpc
description: How to use Isabelle_RPC to call Python functions from Isabelle/ML (contrib/Isabelle_RPC)
---

# Isabelle_RPC: Call Python from Isabelle/ML

Isabelle_RPC lets Isabelle/ML call Python functions via RPC. Communication flows Isabelle → Python (with callbacks). For Python → Isabelle, use Isa-REPL instead.

**Location:** `contrib/Isabelle_RPC`

## Quick Start

1. Start the Python RPC server:
```bash
python contrib/Isabelle_RPC/launcher.py
```

2. In your theory file:
```isabelle
imports Remote_Procedure_Calling
```

3. Call Python procedures from ML code

## Writing RPC Procedures (Python Side)

### Basic Pattern

Register Python functions that Isabelle can call:

```python
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection

@isabelle_remote_procedure("my_function") # the registered procedure name
def my_function(arg, connection: Connection):
    # arg: data sent from Isabelle
    # connection: can be used for callbacks or logging
    result = ... # Your process
    return result  # returned to Isabelle
```

### Examples

```python
@isabelle_remote_procedure("heartbeat")
def _heartbeat_(arg, connection: Connection) -> None:
    connection.server.logger.info(f"Heartbeat from {connection.client_addr}")
    return None

@isabelle_remote_procedure("compute_sum")
def _compute_sum(arg, connection: Connection) -> int:
    # arg is a list of integers from ML
    return sum(arg)
```

## Calling RPC Procedures (Isabelle/ML Side)

### Define a Command

Create a typed command specification with MessagePack schemas:

```sml
type ('a,'b) command = {
  name : string,                           (* registered procedure name *)
  arg_schema : 'a MessagePackBinIO.Pack.packer,     (* argument schema *)
  ret_schema : 'b MessagePackBinIO.Unpack.unpacker, (* return-value schema *)
  callback : (connection -> unit) option,  (* optional callback during call *)
  timeout : Time.time option               (* optional timeout *)
}
```

Examples:

```sml
open MessagePackBinIO.Pack MessagePackBinIO.Unpack

val heartbeat_cmd = {
  name = "heartbeat",
  arg_schema = packUnit,
  ret_schema = unpackUnit,
  callback = NONE,
  timeout = SOME (Time.fromSeconds 10)
}

val compute_sum_cmd = {
  name = "compute_sum",              (* Must match @isabelle_remote_procedure("compute_sum") *)
  arg_schema = packList packInt,     (* Send list of integers *)
  ret_schema = unpackInt,            (* Receive integer result *)
  callback = NONE,
  timeout = SOME (Time.fromSeconds 30)
}
```

### Call the Command

```sml
(* Using connection pool *)
val result = Remote_Procedure_Calling.call_command compute_sum_cmd [1, 2, 3, 4]

(* With explicit connection *)
val conn = Remote_Procedure_Calling.get_connection ()
val result = Remote_Procedure_Calling.call_command' compute_sum_cmd conn [1, 2, 3, 4]
val _ = Remote_Procedure_Calling.release_connection conn
```

## Using Callbacks

Callbacks allow Python to call back into Isabelle during RPC execution. This enables bidirectional communication within a single RPC call.

### Defining Callbacks (Isabelle/ML Side)

Define callbacks that Python can invoke:

```sml
open MessagePackBinIO.Pack MessagePackBinIO.Unpack

val my_callback : (string, int) Remote_Procedure_Calling.callback = {
  name = "my_callback",           (* callback identifier *)
  arg_schema = unpackString,      (* Python → ML schema *)
  ret_schema = packInt,           (* ML → Python schema *)
  function = (fn msg => String.size msg),  (* callback logic *)
  timeout = NONE
}

(* Either register globally using Remote_Procedure_Calling.register_global_callback *)
val _ = Theory.setup (Context.theory_map
  (Remote_Procedure_Calling.register_global_callback my_callback))

(* Or pass as local callback in command definition *)
val my_cmd : (unit, string) Remote_Procedure_Calling.command = {
  name = "my_rpc",
  arg_schema = packUnit,
  ret_schema = unpackString,
  callback = [Remote_Procedure_Calling.mk_callback my_callback],  (* local *)
  timeout = SOME (Time.fromSeconds 10)
}
```

### Calling Callbacks (Python Side)

Invoke Isabelle callbacks from Python RPC procedures:

```python
@isabelle_remote_procedure("my_rpc")
def my_rpc(arg, connection: Connection):
    # Call back to Isabelle's "my_callback"
    result = connection.callback("my_callback", "hello")
    # result = 5 (length of "hello")
    return f"Callback returned: {result}"
```

**Advanced:** For custom bidirectional protocols, define ML callbacks using `callback'` type directly (bypassing structured schemas) and invoke with `connection.raw_callback(name, action)` where `action` is a function receiving the connection for arbitrary I/O operations.

The built-in `isabelle_heartbeat` callback (RPC.ML:328) provides a working example. See `contrib/Isabelle_RPC/test_callback.py` for complete examples.

## Common MessagePack Schemas

### Packing (ML → Python)
- `packUnit` - unit/None
- `packString` - string
- `packInt` - integer
- `packBool` - boolean
- `packReal` - float
- `packList schema` - list
- `packPair (s1, s2)` - 2-tuple
- `packTuple3 (s1, s2, s3)` - 3-tuple
- `packTuple3`, `packTuple4`, `packTuple5` - up to 8-tuple
- `packOption schema` - option/Optional
- `packPairList (s1, s2)` - list of pairs (dict items)

### Unpacking (Python → ML)
- `unpackUnit` - unit/None
- `unpackString` - string
- `unpackInt` - integer
- `unpackBool` - boolean
- `unpackReal` - float
- `unpackList schema` - list
- `unpackPair (s1, s2)` - 2-tuple
- `unpackTuple3 (s1, s2, s3)` - 3-tuple
- `unpackTuple4`, `unpackTuple5` - up to 6-tuple
- `unpackOption schema` - option/Optional
- `unpackPairList (s1, s2)` - list of pairs (dict items)

**Schema reference:** `./contrib/Isabelle_RPC/contrib/mlmsgpack/mlmsgpack.sml`

## Server Configuration

- **Default address:** `127.0.0.1:27182`
- **Change address:** Set `RPC_Host` environment variable (e.g., `export RPC_Host=127.0.0.1:9999`)
- **Auto-launch:** ML code auto-launches server if not running
- **Protocol:** MessagePack over TCP

## Key Files Reference

**Entry points:**
- `Remote_Procedure_Calling.thy` - Main theory file
- `launcher.py` - Server startup script

**Python server:**
- `Isabelle_RPC_Host/__init__.py` - Server implementation and procedure registration

**ML client:**
- `Tools/RPC.ML` - Client implementation (signature `REMOTE_PROCEDURE_CALLING`)

## Relationship with Other Projects

- **Isa-REPL:** Python → Isabelle (opposite direction from RPC)
