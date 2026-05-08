#! /usr/bin/env python3

import asyncio
from tools.server import kill_all_servers, launch_servers

async def main():
    kill_all_servers()
    await launch_servers()

if __name__ == "__main__":
    asyncio.run(main())
