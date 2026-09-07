"""Minimal MCP stdio server that records what the client says about its roots.

On the first request after initialize (list_tools), it logs the client's
InitializeRequestParams (protocolVersion, capabilities, clientInfo), then calls
roots/list on the client (10 s timeout) and logs the answer.  Output is one JSON
document written to $PROBE_LOG.
"""
import asyncio
import json
import os
import sys
import traceback

import mcp.types as types
from mcp.server.lowlevel import Server
from mcp.server.stdio import stdio_server

LOG = os.environ.get("PROBE_LOG", "/dev/stderr")
server = Server("roots-probe")
_done = False


def dump(obj):
    with open(LOG, "w") as f:
        json.dump(obj, f, indent=2, default=str)
        f.write("\n")


async def probe():
    global _done
    if _done:
        return
    _done = True
    session = server.request_context.session
    params = session.client_params
    rec = {
        "server_cwd": os.getcwd(),
        "client_params": params.model_dump(mode="json") if params else None,
    }
    try:
        roots = await asyncio.wait_for(session.list_roots(), 10)
        rec["roots"] = roots.model_dump(mode="json")
    except Exception as e:  # noqa: BLE001
        rec["roots_error"] = repr(e)
        rec["roots_traceback"] = traceback.format_exc()
    dump(rec)


@server.list_tools()
async def list_tools():
    await probe()
    return [types.Tool(name="probe_noop", description="Does nothing.",
                       inputSchema={"type": "object", "properties": {}})]


@server.call_tool()
async def call_tool(name, arguments):
    await probe()
    return [types.TextContent(type="text", text="ok")]


async def main():
    async with stdio_server() as (r, w):
        await server.run(r, w, server.create_initialization_options())


if __name__ == "__main__":
    asyncio.run(main())
