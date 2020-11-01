--------------------------- MODULE CacheInterface ---------------------------

CONSTANT CLIENTS

VARIABLE cache, db, cacheResults, dbResults, cacheWritten, states


Null == "null"
InitValue == "init"
Data == CLIENTS \union {Null, InitValue}

Init == /\ cache = Null
        /\ db = Null
        /\ cacheResults = [c \in CLIENTS |-> Null]
        /\ dbResults = [c \in CLIENTS |-> Null]
        /\ states = [c \in CLIENTS |-> "start"]
        /\ cacheWritten = FALSE
        
TypeOK == /\ cache \in Data
          /\ db \in Data
          /\ Null \notin CLIENTS
          /\ InitValue \notin CLIENTS
        
InitCache == /\ cache = Null
             /\ cache' = db
             /\ UNCHANGED <<db, cacheResults, dbResults, cacheWritten, states>>
             
InitDB == /\ db = Null
          /\ cache = Null
          /\ db' = InitValue
          /\ UNCHANGED <<cache, cacheResults, dbResults, cacheWritten, states>>
        
ReadCache(c) == /\ cacheResults' = [cacheResults EXCEPT ![c] = cache]
                /\ UNCHANGED <<cache, db, dbResults, cacheWritten>>
                
WriteCache(c, v) == /\ cache' = v
                    /\ cacheWritten' = TRUE
                    /\ UNCHANGED <<db, cacheResults, dbResults>>
                    
InvalidateCache == /\ cache' = Null
                   /\ UNCHANGED <<db, cacheResults, dbResults, cacheWritten>>
                    
ReadDb(c) == /\ dbResults' = [dbResults EXCEPT ![c] = db]
             /\ UNCHANGED <<cache, db, cacheResults, cacheWritten>>
             
WriteDB(c, v) == /\ db' = v
                 /\ UNCHANGED <<cache, cacheResults, dbResults, cacheWritten>>
                   
                                  
AllDone == \A c \in CLIENTS: states[c] = "done"
Consistency == IF AllDone THEN (cache = db \/ cache = Null) ELSE TRUE
EventuallyCacheWritten == <>(cacheWritten = TRUE)


=============================================================================
