"""A definition-only async function is never scheduled or called."""


async def never_used():
    await missing


print(0)
