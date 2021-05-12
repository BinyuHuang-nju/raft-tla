--------------------------- MODULE ParallelRaftCE ---------------------------

\* Copyright (c) 2020 Xiaosong Gu

EXTENDS Integers, FiniteSets, Sequences, TLC, Naturals
-----------------------------------------------------------------------------
CONSTANTS Server, Value, Nil

CONSTANTS Follower, Candidate, LeaderCandidate, Leader

CONSTANTS RequestVoteRequest, RequestVoteResponse,
          RequestCommitRequest, RequestCommitResponse,
          RequestSyncRequest, RequestSyncResponse,
          UpdateSyncRequest, UpdateSyncResponse
-----------------------------------------------------------------------------
VARIABLE messages,
         currentTerm,
         currentState,
         votedFor,
         sync,
         endPoint

serverVars == <<currentTerm, currentState, votedFor, sync, endPoint>>

VARIABLE log
logVars == log

VARIABLE syncTrack
leaderVars == syncTrack

VARIABLES halfElections,
          elections
electionVars == <<halfElections, elections>>

VARIABLES allLogs,
          allEntries,
          allSynced     

vars == <<messages, serverVars, logVars, leaderVars, electionVars, allLogs, allEntries, allSynced>> 
-----------------------------------------------------------------------------
Quorums == {i \in SUBSET Server: Cardinality(i)*2 > Cardinality(Server)}

Send(m) == messages' = messages \union {m}

Index == Nat
Term == Nat

Min(s) == IF s = {} THEN -1 
                    ELSE CHOOSE i \in s: \A j \in s: i <= j
Max(s) == IF s = {} THEN -1
                    ELSE CHOOSE i \in s: \A j \in s: i >= j
-----------------------------------------------------------------------------
InitServerVars == /\ currentTerm  = [i \in Server |-> 0]
                  /\ sync         = [i \in Server |-> 0]
                  /\ currentState = [i \in Server |-> Follower]
                  /\ endPoint     = [i \in Server |-> [n \in Term |-> <<-1, -1>>]]
                  /\ votedFor     = [i \in Server |-> Nil]

InitLogVars == log = [i \in Server |-> [n \in Index |-> [term |-> -1,
                                                         date |-> -1,
                                                         value|-> Nil,
                                                         committed |-> FALSE]]]

InitLeaderVars == syncTrack = [i \in Server |-> [j \in Server |-> 0]]

InitHistoryVars == /\ halfElections = {}
                   /\ elections     = {}
                   /\ allLogs       = {}
                   /\ allEntries    = {}
                   /\ allSynced     = {}

Init == /\ messages = {}
        /\ InitServerVars
        /\ InitLogVars
        /\ InitLeaderVars
        /\ InitHistoryVars
-----------------------------------------------------------------------------
 Entries == [term: Term \union {-1}, date: Term \union {-1}, value: Value \union {Nil}, committed: {TRUE, FALSE}]
 
 logTail(s) == Max({i \in Index: s[i].term /= -1})
 
 TypeSafety == /\ allLogs \in SUBSET (SUBSET allEntries)
               /\ currentTerm \in [Server -> Nat]
               /\ currentState \in [Server -> {Follower, Candidate, LeaderCandidate, Leader}]
               /\ votedFor \in [Server -> Server \union {Nil}]
               /\ sync \in [Server -> Nat \union {-1}]
               /\ endPoint \in [Server -> [Term -> ((Term \union {-1}) \times (Index \union {-1}))]]
               /\ log \in [Server -> [Index -> [term: Index \union {-1},
                                                date: Term \union {-1},
                                                value: Value \union {Nil},
                                                committed: {TRUE, FALSE}]]]
               /\ syncTrack \in [Server -> [Server -> Nat]]
               /\ halfElections \subseteq [eterm: Nat, 
                                           eleaderCandidate: Server,
                                           esync: Nat,
                                           evotes: Quorums,
                                           elog: [Index -> Entries]]
               /\ elections \subseteq [eterm: Term, 
                                           esync: Term,
                                           eleader: Server,
                                           evotes: Quorums,
                                           evoterLog: SUBSET [Index -> Entries],
                                           elog: [Index -> Entries]]
 ----------------------------------------------------------------------------
 Restart(i) ==
        /\ currentState' = [currentState EXCEPT ![i] = Follower]
        /\ syncTrack'    = [syncTrack    EXCEPT ![i] = [j \in Server |-> 0]]
        /\ UNCHANGED << messages,currentTerm, votedFor, sync, endPoint, log, electionVars, allSynced>>
 
 Timeout(i) ==
        /\ currentState[i] \in {Follower, Candidate}
        /\ currentState' = [currentState EXCEPT ![i] = Candidate]
        /\ currentTerm'  = [currentTerm  EXCEPT ![i] = currentTerm[i] + 1]
        /\ (currentTerm[i] + 1) \in Term
        /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
        /\ UNCHANGED <<messages, sync, endPoint, logVars, leaderVars, electionVars, allSynced>>
        
UpdateTerm(i) ==
        /\ \E m \in messages:
                /\ m.mterm > currentTerm[i]
                /\ \/ m.mdest = i
                   \/ m.mdest = Nil
                /\ currentState' = [currentState EXCEPT ![i] = Follower]
                /\ currentTerm'  = [currentTerm  EXCEPT ![i] = m.mterm]
                /\ votedFor'     = [votedFor     EXCEPT ![i] = Nil]
        /\ UNCHANGED <<messages, sync, logVars, leaderVars, electionVars, allSynced, endPoint>>
 ----------------------------------------------------------------------------
 
RequestVote(i) ==
        /\ currentState[i] = Candidate
        /\ Send([mtype   |-> RequestVoteRequest,
                 mterm   |-> currentTerm[i],
                 msync   |-> sync[i],
                 msource |-> i,
                 mdest   |-> Nil])
        /\ UNCHANGED<<serverVars, leaderVars, logVars, electionVars, allSynced>>

HandleRequestVoteRequest(i) ==
        /\ \E m \in messages:
            LET j == m.msource
                syncOK == m.msync >= sync[i]
                grant == /\ syncOK
                         /\ votedFor[i] \in {Nil, j}
                         /\ currentTerm[i] = m.mterm
            IN /\ m.mterm <= currentTerm[i]
               /\ m.mtype = RequestVoteRequest
               /\ \/ /\ grant
                     /\ votedFor' = [votedFor EXCEPT ![i] = j]
                  \/ /\ ~grant
                     /\ UNCHANGED votedFor
               /\ Send([mtype        |-> RequestVoteResponse,
                        mterm        |-> currentTerm[i],
                        mvoteGranted |-> grant,
                        mlog         |-> LET C == {n \in Index: log[i][n].term = sync[i]}
                                         IN {<<n, log[i][n]>>: n \in C},
                        mend         |-> endPoint[i][m.msync],
                        msource      |-> i,
                        mdest        |-> j])
        /\ UNCHANGED <<currentTerm, currentState, sync, logVars, leaderVars, electionVars, allSynced, endPoint>>

Merge(entries, term, date) == IF entries = {} THEN [term      |-> term,
                                                    date      |-> date,
                                                    value     |-> Nil,
                                                    committed |-> FALSE]
                              ELSE LET committed == {e \in entries: e.committed = TRUE}
                                       chosen == CASE committed =  {} -> CHOOSE x \in entries:
                                                                            \A y \in entries: x.date >= y.date
                                                 []   committed /= {} -> CHOOSE x \in committed: TRUE 
                                   IN [term      |-> chosen.term,
                                       date      |-> date,
                                       value     |-> chosen.value,
                                       committed |-> chosen.committed]  

BecomeLeaderCandidate(i) ==
        /\ currentState[i] = Candidate
        /\ \E P,Q \in Quorums:
            LET voteResponded == {m \in messages: /\ m.mtype = RequestVoteResponse
                                                  /\ m.mdest = i
                                                  /\ m.msource \in P
                                                  /\ m.mterm = currentTerm[i]}
                voteGranted   == {m \in voteResponded: /\ m.mvoteGranted = TRUE
                                                       /\ m.msource \in Q}
                allLog        == UNION {m.mlog: m \in voteResponded}
                end           == LET allPoint == {m.mend: m \in voteResponded}      \* end, endPoint
                                     e        == CHOOSE e1 \in allPoint: \A e2 \in allPoint: e1[1] >= e2[1]
                                 IN IF e[1] = -1 THEN Max({e1[1]: e1 \in allLog})
                                                 ELSE e[2]
                toRecover     == {n \in 0..end: log[i][n].committed = FALSE}
                toSync        == {<<n, Merge({l[2]: l \in {t \in allLog: t[1] = n}}, sync[1], currentTerm[i])>> : n \in toRecover}
            IN /\ \A q \in Q: \E m \in voteGranted: m.msource = q
               /\ log' = [log EXCEPT ![i] = IF end = -1 THEN [n \in Index |-> IF log[i][n].term = sync[i] THEN [term      |-> -1,
                                                                                                                date      |-> -1,
                                                                                                                value     |-> Nil,
                                                                                                                committed |-> FALSE]
                                                                                                          ELSE log[i][n]]
                                                        ELSE [n \in Index |-> IF n \in toRecover THEN (CHOOSE e \in toSync: e[1] = n)[2]
                                                                              ELSE IF n > end THEN [term      |-> -1,
                                                                                                    date      |-> -1,
                                                                                                    value     |-> Nil,
                                                                                                    committed |-> FALSE]
                                                                                              ELSE log[i][n]]]
               /\ endPoint' = [endPoint EXCEPT ![i][sync[i]] = <<currentTerm[i], end>>]
               /\ halfElections' = halfElections \union {[eterm            |-> currentTerm[i],
                                                          eleaderCandidate |-> i,
                                                          esync            |-> sync[i],
                                                          evotes           |-> Q,
                                                          elog             |-> log[i]]}
        /\ currentState' = [currentState EXCEPT ![i] = LeaderCandidate]
        /\ syncTrack'    = [syncTrack    EXCEPT ![i] = [j \in Server |-> sync[i]]] \* here
        /\ UNCHANGED <<messages, currentTerm, votedFor, sync, elections, allSynced>>

-----------------------------------------------------------------------------
RequestSync(i) ==
        /\ currentState[i] \in {LeaderCandidate, Leader}
        /\ \E s \in 0..sync[i]:
            LET start == Min({n \in Index: log[i][n].term = s})
                end   == Max({n \in Index: log[i][n].term = s})                \* here
            IN /\ Send([mtype    |-> RequestSyncRequest,
                        mterm    |-> currentTerm[i],
                        msync    |-> s,
                        mstart   |-> start,
                        mend     |-> end,
                        mentries |-> IF start = -1 THEN Nil 
                                                   ELSE [n \in start..end |->log[i][n]],
                        msource  |-> i,
                        mdest    |-> Nil])                 \* here
        /\ UNCHANGED <<serverVars, logVars, electionVars, syncTrack, allSynced>>

HandleRequestSyncRequest(i) ==
        /\ \E m \in messages:
            LET j     == m.msource
                grant == /\ m.mterm = currentTerm[i]
                         /\ m.msync = sync[i]
            IN /\ m.mtype = RequestSyncRequest
               /\ m.mterm <= currentTerm[i]
               /\ j /= i
               /\ \/ /\ grant
                     /\ log' = [log EXCEPT ![i] = IF m.mstart = -1 THEN [n \in Index |-> IF log[i][n].term = sync[i] THEN [term |-> -1,
                                                                                                                           date |-> -1,
                                                                                                                           vallue |-> Nil,
                                                                                                                           committed |-> FALSE]
                                                                                                                     ELSE log[i][n]]
                                                                   ELSE [n \in Index |-> IF n < m.mstart THEN log[i][n]
                                                                                         ELSE IF n \in m.mstart..m.mend THEN m.mentries[n]
                                                                                         ELSE [term |-> -1,
                                                                                               date |-> -1,
                                                                                               value |-> Nil,
                                                                                               committed |->FALSE]]]
                     /\ endPoint' = [endPoint EXCEPT ![i][sync[i]] = <<currentTerm[i], m.mend>>]
                  \/ /\ ~grant
                     /\ UNCHANGED <<log, endPoint>>
               /\ Send([mtype        |-> RequestSyncResponse,
                        mterm        |-> currentTerm[i],
                        msyncGranted |-> grant,
                        msync        |-> sync[i],
                        mstart       |-> m.mstart,
                        mend         |-> m.mend,
                        msource      |-> i,
                        mdest        |-> j])
        /\ UNCHANGED <<currentTerm,currentState,sync,votedFor,electionVars,syncTrack,allSynced>>

HandleRequestSyncResponse(i) ==
        /\ \E m \in messages:
            LET j == m.msource 
            IN /\ m.mtype = RequestSyncResponse
               /\ m.mdest = i
               /\ currentTerm[i] = m.mterm
               /\ currentState[i] \in {LeaderCandidate, Leader}
               /\ syncTrack' = [syncTrack EXCEPT ![i][j] = m.msync]
               /\ \/ /\ m.msyncGranted
                     /\ m.msync < sync[i]
                     /\ Send([mtype   |-> UpdateSyncRequest,
                              mterm   |-> currentTerm[i],
                              msync   |-> Min({sync[i]} \union {k \in Nat: /\ k > m.msync
                                                                           /\ Cardinality({n \in Index: log[i][n].term = k}) > 0}), \* here 1
                              msource |-> i,
                              mdest   |-> {j}])
                  \/ /\ ~m.msyncGranted
                     /\ UNCHANGED messages
        /\ UNCHANGED <<serverVars,logVars,electionVars,allSynced>>

-----------------------------------------------------------------------------
UpdateSync(i) ==
        /\ currentState[i] = LeaderCandidate
        /\ \E Q \in Quorums:
            LET syncUpdated == {m \in messages: /\ m.mtype = RequestSyncResponse
                                                /\ m.mterm = currentTerm[i]
                                                /\ m.msyncGranted = TRUE
                                                /\ m.msync = sync[i]
                                                /\ m.msource \in Q
                                                /\ m.mdest = i}
            IN /\ \A q \in Q: \/ \E m \in syncUpdated: m.msource = q
                              \/ q = i
               /\ allSynced' = LET indexes == {n \in Index: log[i][n].term = sync[i]}
                                   entries == {<<n, [term      |-> log[i][n].term,
                                                     date      |-> log[i][n].date,
                                                     value     |-> log[i][n].value,
                                                     committed |-> TRUE]>>: n \in indexes}
                               IN allSynced \union {<<sync[i], endPoint[i][sync[i]][2], entries>>}  
               /\ Send([mtype   |-> UpdateSyncRequest,
                        mterm   |-> currentTerm[i],
                        msync   |-> currentTerm[i],  \* here 2
                        msource |-> i,
                        mdest   |-> Q])    
        /\ UNCHANGED <<serverVars,logVars,leaderVars,electionVars>>      

HandleUpdateSyncRequest(i) ==
        \E m \in messages:
            LET j     == m.msource
                grant == /\ currentTerm[i] = m.mterm
                         /\ m.msync > sync[i]
            IN /\ m.mtype = UpdateSyncRequest
               /\ i \in m.mdest
               /\ m.mterm <= currentTerm[i]
               /\ \/ /\ grant
                     /\ sync' = [sync EXCEPT ![i] = m.msync]          \* here
                     /\ log'  = [log EXCEPT ![i] = [n \in Index |-> IF log[i][n].term = sync[i] THEN [term |-> log[i][n].term,
                                                                                                      date |-> log[i][n].date,
                                                                                                      value |-> log[i][n].value,
                                                                                                      committed |-> TRUE]
                                                                                                ELSE log[i][n]]] 
                  \/ /\ ~grant
                     /\ UNCHANGED <<log, sync>>
               /\ Send([mtype |-> UpdateSyncResponse,
                        mterm |-> currentTerm[i],
                        mupdateSyncGranted |-> grant,
                        msync |-> sync'[i],
                        msource |-> i,
                        mdest |-> j])
        /\ UNCHANGED <<currentTerm,currentState,votedFor,endPoint,leaderVars,electionVars,allSynced>>

HandleUpdateSyncResponse(i) ==
        /\ \E m \in messages:
            LET j == m.msource 
            IN /\ m.mtype = UpdateSyncResponse
               /\ m.mdest = i
               /\ currentTerm[i] = m.mterm
               /\ currentState[i] \in {Leader, LeaderCandidate}
               /\ \/ /\ m.mupdateSyncGranted
                     /\ syncTrack' = [syncTrack EXCEPT ![i][j] = m.msync]
                  \/ /\ ~m.mupdateSyncGranted
                     /\ UNCHANGED syncTrack
        /\ UNCHANGED <<messages,serverVars,logVars,electionVars,allSynced>>

-----------------------------------------------------------------------------
BecomeLeader(i) ==
        /\ currentState[i] = LeaderCandidate
        /\ \E Q \in Quorums:
            /\ \A q \in Q: \/ q = i
                        \/ syncTrack[i][q] = currentTerm[i]
            /\ elections' = elections \union {[eterm |-> currentTerm[i],
                                               esync |-> sync[i],     \* here
                                               eleader |-> i,
                                               evotes |-> Q,
                                               evoterLog |-> {log[k]: k \in Q},
                                               elog |-> log[i]]}
        /\ sync' = [sync EXCEPT ![i] = currentTerm[i]]
        /\ currentState' = [currentState EXCEPT ![i] = Leader]
        /\ log' = [log EXCEPT ![i] = [n \in Index |-> IF log[i][n].term = sync[i] THEN [term |-> log[i][n].term,
                                                                                        date |-> log[i][n].date,
                                                                                        vallue |-> log[i][n].value,
                                                                                        committed |-> TRUE]
                                                                                  ELSE log[i][n]]]
        /\ UNCHANGED <<messages,currentTerm,votedFor,endPoint,leaderVars,halfElections,allSynced>>

-----------------------------------------------------------------------------        
ClientRequest(i, v) ==
        /\ LET nextIndex == logTail(log[i]) + 1
               entry     == [term |-> currentTerm[i],
                             date |-> currentTerm[i],
                             value |-> v,
                             committed |-> FALSE]
           IN /\ currentState[i] = Leader
              /\ nextIndex \in Nat
              /\ log' = [log EXCEPT ![i][nextIndex] = entry]
              /\ UNCHANGED <<messages,serverVars,electionVars,syncTrack,allSynced>>

CommitEntry(i, n) ==
        /\ \E Q \in Quorums:
            LET succ == {m \in messages: /\ m.mtype = RequestSyncResponse
                                         /\ m.msyncGranted = TRUE
                                         /\ m.mdest = i
                                         /\ m.mterm = currentTerm[i]
                                         /\ m.msource \in Q
                                         /\ n \in m.mstart..m.mend}
            IN /\ \A q \in Q: \E m \in succ: \/ q = i
                                             \/ m.msource = q
               /\ log' = [log EXCEPT ![i][n].committed = TRUE]
        /\ currentState[i] = Leader
        /\ UNCHANGED <<messages,serverVars,log,syncTrack,electionVars,allSynced>>

-----------------------------------------------------------------------------
Next ==     /\
               \/ \E i \in Server: Restart(i)
               \/ \E i \in Server: Timeout(i)
               \/ \E i \in Server: UpdateTerm(i)
               \/ \E i \in Server: RequestVote(i)
               \/ \E i \in Server : HandleRequestVoteRequest(i)
               \/ \E i \in Server : BecomeLeaderCandidate(i)
               \/ \E i \in Server : BecomeLeader(i)
               \/ \E i \in Server, v \in Value : ClientRequest(i,v)
               \/ \E i,j \in Server : RequestSync(i)
               \/ \E i \in Server : HandleRequestSyncRequest(i)
               \/ \E i \in Server : HandleRequestSyncResponse(i)
               \/ \E i,j \in Server : UpdateSync(i)
               \/ \E i \in Server : HandleUpdateSyncRequest(i)
               \/ \E i \in Server : HandleUpdateSyncResponse(i)
               
           /\  allLogs' = allLogs \union {log[i] : i \in Server}
           /\ LET entries(i) == {<<n, log[i][n]>>: n \in Index}
              IN allEntries' = allEntries \union UNION {entries(i): i \in Server}
              
Spec == Init/\ [][Next]_vars

-----------------------------------------------------------------------------
AllEntries(i) == {<<n,log[i][n]>> : n \in Index} 

Lemma1 == \A i \in Server : sync[i] \leq currentTerm[i]
Lemma2 == \A i \in Server : currentState[i]=Leader => sync[i] = currentTerm[i]
Lemma3 == \A e,f \in halfElections : e.eterm = f.eterm => e.eleaderCandidate = f.eleaderCandidate
Lemma4 == \A e \in elections : \E f \in halfElections : e.eterm = f.eterm
                                         /\ e.eleader = f.eleaderCandidate
Lemma5 == \A e,f \in elections : e.eterm = f.eterm => e.eleader = f.eleader
Lemma6 == \forall i \in Server : currentState[i]=Leader => currentTerm[i] = sync[i]
Lemma7 == \A e \in halfElections : e.esync < e.eterm
Lemma8 == \A i,j \in Server, n \in Index : log[i][n].term = log[j][n].term => 
                                           log[i][n].value = log[j][n].value
Lemma9 == \A s1,s2 \in allSynced : s1[1]=s2[1] => s1=s2
Lemma10 == \A e1,e2 \in elections : e1.eterm < e2.eterm =>
            \E s \in allSynced : s[1] = e1.term
Lemma11 == LET indexes(i,t) == {n \in Index : log[i][n].term=t} 
               entries(i,t) == {<<n,log[i][n]>> : n \in indexes(i,t)} IN
            \A i \in Server : \A t \in Term :
            t < sync[i] /\ (\E e \in elections : e.eterm = t) => \E s \in allSynced : s[1] = t /\
              entries(i,t) = s[3]
Lemma12 == \A i \in Server : \A e \in AllEntries(i) :  e[2].term \leq sync[i]
Lemma13 == \A e \in halfElections : \A f \in elections : f.eterm \leq e.esync \/ f.eterm \geq e.eterm
syncCompleteness == \A i,j \in Server :  
        {e \in AllEntries(i) : e[2].term \geq 0 /\ e[2].term < Min({sync[i],sync[j]})} = 
        {e \in AllEntries(j) : e[2].term \geq 0 /\ e[2].term < Min({sync[i],sync[j]})}
=============================================================================
\* Modification History
\* Last modified Wed May 12 22:25:17 CST 2021 by Dell
\* Created Tue May 11 22:35:25 CST 2021 by Dell
