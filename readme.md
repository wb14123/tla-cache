
In web development, it's very usual to use a cache in front of a database. The cache and database are read/write by multiple clients at the same time.

```
client1  -->
client2  -->   cache  --> database
...      -->
client_n -->
```

In this project, we use TLA+ to specify different cache algorithms, and use TLC to verify the consistency between cache and database.

## Run

Download the tla tools and use tlc to run the models. For example, to run model check on WriteInvalidateCache, run this command:

```
tlc WriteInvalidateCache
```

This should fail because it doesn't meet invariant `Consistency`.
