# Literal-initialized invalid packed dimensions

A malformed integral packed dimension is rejected during elaboration. When its initializer is a direct integral literal, the declaration still has no runtime object, so the legacy envelope omits it. Effectful initializers remain loud.
