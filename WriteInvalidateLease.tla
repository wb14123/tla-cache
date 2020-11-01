------------------------ MODULE WriteInvalidateLease ------------------------

(*

This algorithm uses lease while write back to cache during cache miss.

It's based on the paper "Scaling Memcache at Facebook".

The "atomic" part in the pseudocode must be atomic across the hosts. Which means
this part is normally implemented by cache. It implement an atomic read API that
returns the lease token with cache (or cache miss) to clients. Clients then use
another atomic write API to write cache with the lease token.

*)

CONSTANT CLIENTS

VARIABLE cache, db, cacheResults, dbResults, cacheWritten, states, lease

INSTANCE CacheInterface

------------------------------------------------------------------------------

(*

This specify a read algorithm with this pseudocode:

read(client, key) {
    atomic {
        lease = generate_uniq_id()
        cache = readCache(key)
        setLease(key) = lease
    }
    if (cache != null) {
        return cache
    }
    data = readDB(key)
    atomic {
        if (getLease(key) == lease) {
            writeCache(key, data)
        }
        setLease(key) = null
    }
    return data
}

*)

LeaseInit == /\ Init
             /\ lease = Null


ReadCacheFirst(c) == /\ states[c] = "start"
                     /\ ReadCache(c)
                     /\ lease' = c
                     /\ states' = [states EXCEPT ![c] = "check_cache"]
                     
ReadWithCacheHit(c) == /\ states[c] = "check_cache"
                       /\ cacheResults[c] # Null
                       /\ states' = [states EXCEPT ![c] = "done"]
                       /\ UNCHANGED <<cache, db, cacheResults, dbResults, cacheWritten, lease>>
                    
                        
ReadDBWithCacheMiss(c) == /\ states[c] = "check_cache"
                          /\ cacheResults[c] = Null
                          /\ ReadDb(c)
                          /\ states' = [states EXCEPT ![c] = "write_back_cache"]
                          /\ UNCHANGED lease
                         
                          
ReadWriteBackCache(c) == /\ lease = c
                         /\ states[c] = "write_back_cache"
                         /\ WriteCache(c, dbResults[c])
                         /\ states' = [states EXCEPT ![c] = "done"]
                         /\ lease' = Null        
                         
                         
ReadWriteBackCacheNoLease(c) == /\ lease # c
                                /\ states[c] = "write_back_cache"
                                /\ states' = [states EXCEPT ![c] = "done"]
                                /\ lease' = Null   
                                /\ UNCHANGED <<cache, db, cacheResults, dbResults, cacheWritten>>                                                                                                                             
                         
                         
Read(c) == \/ ReadCacheFirst(c)
           \/ ReadWithCacheHit(c)
           \/ ReadDBWithCacheMiss(c)
           \/ ReadWriteBackCache(c)
           \/ ReadWriteBackCacheNoLease(c)
           
------------------------------------------------------------------------------


(*

This specify a read algorithm with this pseudocode:

write(key, value) {
    writeDB(key, value)
    atomic {
        invalidateCache(key)
        setLease(key) = null
    }
}

*)

           
           
WriteFirst(c) == /\ states[c] = "start"
                 /\ WriteDB(c, c)
                 /\ states' = [states EXCEPT ![c] = "invalide_cache"]
                 /\ UNCHANGED lease
                 
WriteInvalideCache(c) == /\ states[c] = "invalide_cache"
                         /\ InvalidateCache
                         /\ states' = [states EXCEPT ![c] = "done"]
                         /\ lease' = Null
                         
                         
Write(c) == \/ WriteFirst(c)
            \/ WriteInvalideCache(c)
            
------------------------------------------------------------------------------
            
Restart(c) == /\ states[c] = "done"
              /\ states' = [states EXCEPT ![c] = "start"]
              /\ UNCHANGED <<cache, db, cacheResults, dbResults, cacheWritten, lease>>
              
              
InitCacheWithLease == /\ InitCache
                      /\ UNCHANGED lease
                     

InitDBWithLease == /\ InitDB
                   /\ UNCHANGED lease


Next == \E c \in CLIENTS: \/ Read(c)
                          \/ Write(c)
                          \/ Restart(c)
                          \/ InitCacheWithLease
                          \/ InitDBWithLease
                          
Spec == /\ LeaseInit
        /\ [][Next]_<<cache, db, cacheResults, dbResults, cacheWritten, states, lease>>
        /\ WF_<<cache, db, cacheResults, dbResults, cacheWritten, states, lease>>(Next)
        
THEOREM Spec => []TypeOK /\ []Consistency


                        
=============================================================================
