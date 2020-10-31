------------------------ MODULE WriteInvalidateCache ------------------------

CONSTANT CLIENTS

VARIABLE cache, db, cacheResults, dbResults, cacheWritten, states

INSTANCE CacheInterface

------------------------------------------------------------------------------

(*

This specify a read algorithm with this pseudocode:

read(key) {
    cache = readCache(key)
    if (cache != null) {
        return cache
    }
    data = readDB(key)
    writeCache(key, data)
    return data
}

*)




ReadCacheFirst(c) == /\ states[c] = "start"
                     /\ ReadCache(c)
                     /\ states' = [states EXCEPT ![c] = "check_cache"]
                     
ReadWithCacheHit(c) == /\ states[c] = "check_cache"
                       /\ cacheResults[c] # Null
                       /\ states' = [states EXCEPT ![c] = "done"]
                       /\ UNCHANGED <<cache, db, cacheResults, dbResults, cacheWritten>>
                    
                        
ReadDBWithCacheMiss(c) == /\ states[c] = "check_cache"
                          /\ cacheResults[c] = Null
                          /\ ReadDb(c)
                          /\ states' = [states EXCEPT ![c] = "write_back_cache"]
                          
ReadWriteBackCache(c) == /\ states[c] = "write_back_cache"
                         /\ WriteCache(c, dbResults[c])
                         /\ states' = [states EXCEPT ![c] = "done"]
                         
                         
Read(c) == \/ ReadCacheFirst(c)
           \/ ReadWithCacheHit(c)
           \/ ReadDBWithCacheMiss(c)
           \/ ReadWriteBackCache(c)
           
------------------------------------------------------------------------------


(*

This specify a read algorithm with this pseudocode:

write(key, value) {
    writeDB(key, value)
    invalidateCache(key)
}

*)

           
           
WriteFirst(c) == /\ states[c] = "start"
                 /\ WriteDB(c, c)
                 /\ states' = [states EXCEPT ![c] = "invalide_cache"]
                 
WriteInvalideCache(c) == /\ states[c] = "invalide_cache"
                         /\ InvalidateCache
                         /\ states' = [states EXCEPT ![c] = "done"]
                         
                         
Write(c) == \/ WriteFirst(c)
            \/ WriteInvalideCache(c)
            
------------------------------------------------------------------------------
            
Restart(c) == /\ states[c] = "done"
              /\ states' = [states EXCEPT ![c] = "start"]
              /\ UNCHANGED <<cache, db, cacheResults, dbResults, cacheWritten>>


Next == \E c \in CLIENTS: \/ Read(c)
                          \/ Write(c)
                          \/ Restart(c)
                          \/ InitCache
                          \/ InitDB
                          
Spec == Init /\ [][Next]_<<cache, db, cacheResults, dbResults, cacheWritten, states>>
THEOREM Spec => []TypeOK /\ []Consistency


                        
=============================================================================
