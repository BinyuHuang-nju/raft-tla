--------------------------- MODULE ParallelRaftSE ---------------------------

\* Copyright (c) 2020 Xiaosong Gu

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANT Server

CONSTANT Value 

CONSTANTS Follower, Candidate, Leader, LeaderCandidate, Nil
------------------------------------------------------------------------------
Quorums == {i \in SUBSET Server: Cardinality(i)*2 > Cardinality(Server)}

Index == {0, 1, 2, 3, 4, 5, 6}

Term == Nat

------------------------------------------------------------------------------
VARIABLES r1amsgs,
          r1bmsgs,
          r2amsgs,
          r2bmsgs,
          r3amsgs,
          negMsgs,
          currentTerm,
          currentState,
          vote,
          leaderLog,
          log

msgsVars == <<r1amsgs, r1bmsgs, r2amsgs, r2bmsgs, r3amsgs>>     
serverVars == <<currentTerm, currentState>>
vars == <<msgsVars, serverVars, negMsgs, vote, leaderLog, log>>

------------------------------------------------------------------------------
Max(s) == CHOOSE i \in s: \A j \in s: i >= j

lastIndex(i) == IF {b \in Index: log[i][b][1] /= -1} = {} THEN -1
                ELSE Max({b \in Index: log[i][b][1] /= -1})

allEntries == {<<t,v,b>>: t \in Term \union {-1}, v \in Value \union {Nil}, b \in {TRUE,FALSE}}
logEntries == {<<i,e>>: i \in Index, e \in allEntries}

TypeInv == /\ currentTerm \in [Server -> Nat]
           /\ currentState \in [Server -> {Follower, Leader, LeaderCandidate, Candidate}]
           /\ log \in [Server -> [Index -> (Term \union {-1}) \times (Value \union {Nil}) \times BOOLEAN]]
           /\ r1amsgs \subseteq {<<t,i>>: t \in Term, i \in Server}
           /\ r1bmsgs \subseteq {<<t,e,i,j>>: t \in Term, e \in SUBSET logEntries, i \in Server, j \in Server}
           /\ r2amsgs \subseteq {<<t,n,e,i>>: t \in Term, n \in Index, e \in allEntries, i \in Server}
           /\ r2bmsgs \subseteq {<<t,n,i,j>>: t \in Term, n \in Index, i \in Server, j \in Server}
           /\ r3amsgs \subseteq {<<t,n,i>>: t \in Term, n \in Index, i \in Server}
           /\ negMsgs \subseteq {<<t,i>>: t \in Term, i \in Server}
           /\ log \in [Server -> [Index -> allEntries]]
           /\ leaderLog \in [Term -> [Index -> allEntries]]
           /\ vote \in [Server -> [Index -> [Term -> Value \union {Nil}]]]

------------------------------------------------------------------------------
Init == /\ r1amsgs = {}
        /\ r1bmsgs = {}
        /\ r2amsgs = {}
        /\ r2bmsgs = {}
        /\ r3amsgs = {}
        /\ negMsgs = {}
        /\ currentTerm = [i \in Server |-> 0]
        /\ currentState = [i \in Server |-> Follower]
        /\ vote = [i \in Server |-> [j \in Index |-> [t \in Term |-> Nil]]]
        /\ leaderLog = [i \in Term |-> [j \in Index |-> <<-1,Nil,FALSE>>]]
        /\ log = [i \in Server |-> [j \in Index |-> <<-1,Nil,FALSE>>]]

------------------------------------------------------------------------------
Restart(i) == /\ currentState' = [currentState EXCEPT ![i] = Follower]
              /\ UNCHANGED <<msgsVars, currentTerm, negMsgs, vote, leaderLog, log>>

UpdateTerm(i, b) ==
        /\ currentTerm[i] < b
        /\ currentTerm'  = [currentTerm  EXCEPT ![i] = b]
        /\ currentState' = [currentState EXCEPT ![i] = Follower]

ReceiveHighTerm(i) == 
        /\ \E m \in negMsgs: /\ m[i] > currentTerm[i]
                             /\ m[2] = i
                             /\ UpdateTerm(i, m[1])
        /\ UNCHANGED <<msgsVars, negMsgs, vote, leaderLog, log>>
        
Timeout(i) ==
        /\ currentState[i] \in {Follower, Candidate}
        /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
        /\ currentState' = [currentState EXCEPT ![i] = Candidate]
        /\ (currentTerm[i] + 1) \in Nat
        /\ UNCHANGED <<msgsVars, negMsgs, vote, leaderLog, log>>
        
RequestVote(i) ==
        /\ currentState[i] = Candidate
        /\ r1amsgs' = r1amsgs \union {<<currentTerm[i], i>>}
        /\ UNCHANGED <<serverVars, r1bmsgs, r2amsgs, r2bmsgs, r3amsgs, negMsgs, log, leaderLog, vote>>

HandleRequestVoteRequest(i) ==
        /\ \E m \in r1amsgs:
            LET j == m[2]
                grant == m[1] > currentTerm[i]
                entries == {<<n, log[i][n]>>: n \in Index}
            IN 
             \/ /\ grant
                /\ UpdateTerm(i, m[1])
                /\ r1bmsgs' = r1bmsgs \union {<<m[1], entries, i, j>>}
                /\ UNCHANGED negMsgs
             \/ /\ ~grant
                /\ negMsgs' = negMsgs \union {<<currentTerm[i], j>>}
                /\ UNCHANGED <<currentState, currentTerm, r1bmsgs>>
        /\ UNCHANGED <<log,r1amsgs, r2amsgs, r2bmsgs, r3amsgs, vote, leaderLog>>

Merge(entries, term, v) ==
        LET committed == {e \in entries: e[3] = TRUE}
            chosen == CASE committed =  {} -> CHOOSE x \in entries: \A y \in entries: x[1] >= y[1]
                      []   committed /= {} -> CHOOSE x \in committed: TRUE
            safe == IF chosen[2] = Nil THEN v ELSE chosen[2]
        IN <<term, safe, chosen[3]>>
                
BecomeLeaderCandidate(i) ==
        /\ currentState[i] = Candidate
        /\ \E Q \in Quorums:
            LET voteGranted == {m \in r1bmsgs: m[4] = i /\ m[3] \in Q /\ m[1] = currentTerm[i]}   \* <<m[1], entries, i, j>>
                allLog      == UNION {m[2]: m \in voteGranted}                                    \* <<n, log[i][n]>>
                valid       == {e \in allLog: e[2][1] /= -1}                                      \* log[i][n]: <<t,v,b>>
                end         == IF valid = {} THEN -1 ELSE Max({e[1]: e \in valid})
            IN
                /\ \A q \in Q: \E m \in voteGranted: m[3] = q
                /\ \E v \in Value: leaderLog' = [leaderLog EXCEPT ![currentTerm[i]] = [n \in Index |-> 
                                                                    IF n \in 0..end THEN Merge({l[2]: l \in {t \in allLog: t[1] = n}}, currentTerm[i], v)
                                                                                    ELSE <<-1, Nil, FALSE>>]]
        /\ currentState' = [currentState EXCEPT ![i] = LeaderCandidate]
        /\ UNCHANGED <<currentTerm, log, msgsVars, vote, negMsgs>>

RequestSync(i) ==
        /\ currentState[i] \in {LeaderCandidate, Leader}
        /\ LET sync == {n \in Index: leaderLog[currentTerm[i]][n][1] /= -1}
           IN \E n \in sync: r2amsgs' = r2amsgs \union {<<currentTerm[i], n, leaderLog[currentTerm[i]][n], i>>}
        /\ UNCHANGED <<serverVars, log, leaderLog, vote, r1amsgs, r1bmsgs, r2bmsgs, r3amsgs, negMsgs>>

HandleRequestSyncRequest(i) ==
        /\ \E m \in r2amsgs:                     \* <<currentTerm[i], n, leaderLog[currentTerm[i]][n], i>>
            LET j     == m[4]
                grant == m[1] >= currentTerm[i]
            IN /\ \/ /\ m[1] > currentTerm[i]
                     /\ UpdateTerm(i, m[1])
                  \/ /\ m[1] <= currentTerm[i]
                     /\ UNCHANGED <<currentTerm, currentState>>
               /\ \/ /\ grant
                     /\ log' = [log EXCEPT ![i][m[2]] = m[3]]
                     /\ vote' = [vote EXCEPT ![i][m[2]][m[1]] = m[3][2]]
                     /\ r2bmsgs' = r2bmsgs \union {<<m[1] ,m[2], i, j>>}
                     /\ UNCHANGED negMsgs
                  \/ /\ ~grant
                     /\ negMsgs' = negMsgs \union {<<currentTerm[i], j>>}
                     /\ UNCHANGED <<log, vote, r2bmsgs>>
        /\ UNCHANGED <<r1amsgs, r1bmsgs, r2amsgs, r3amsgs, leaderLog>>

CommitEntry(i) ==
        /\ currentState[i] \in {Leader, LeaderCandidate}
        /\ \E index \in Index, Q \in Quorums:
            LET syncSuccess == {m \in r2bmsgs: /\ m[4] = i 
                                               /\ m[3] \in Q
                                               /\ m[1] = currentTerm[i]
                                               /\ m[2] = index}
            IN /\ \A q \in Q: \E m \in syncSuccess: m[3] = q
               /\ leaderLog' = [leaderLog EXCEPT ![currentTerm[i]][index][3] = TRUE]
        /\ UNCHANGED <<serverVars, log, msgsVars, negMsgs, vote>>

RequestCommit(i) ==
        /\ currentState[i] \in {Leader, LeaderCandidate}
        /\ LET committed == {n \in Index: leaderLog[currentTerm[i]][n][3] = TRUE}
           IN \E n \in committed:
                r3amsgs' = r3amsgs \union {<<currentTerm[i], n, i>>}
        /\ UNCHANGED <<serverVars, log, r1amsgs, r1bmsgs, r2amsgs, r2bmsgs, negMsgs, leaderLog, vote>>

HandleRequestCommitRequest(i) ==
        /\ \E m \in r3amsgs:
            LET j == m[3]
                grant == currentTerm[i] <= m[1]
            IN /\ \/ /\ m[1] > currentTerm[i]
                     /\ UpdateTerm(i, m[1])
                  \/ /\ m[1] <= currentTerm[i]
                     /\ UNCHANGED <<currentTerm, currentState>>
               /\ \/ /\ grant
                     /\ log[i][m[2]][1] = m[1]
                     /\ log' = [log EXCEPT ![i][m[2]][3] = TRUE]
                     /\ UNCHANGED negMsgs
                  \/ /\ ~grant
                     /\ negMsgs' = negMsgs \union {<<currentTerm[i], j>>}
                     /\ UNCHANGED log
        /\ UNCHANGED <<msgsVars, leaderLog, vote>>

BecomeLeader(i) ==
        /\ currentState[i] = LeaderCandidate
        /\ currentState' = [currentState EXCEPT ![i] = Leader]
        /\ UNCHANGED <<currentTerm, log, msgsVars, negMsgs, leaderLog, vote>>
        
ClientRequest(i) ==
        LET ind == {b \in Index: leaderLog[currentTerm[i]][b][1] /= -1}
            nextIndex == IF ind = {} THEN 0
                                     ELSE Max(ind) + 1
        IN /\ currentState[i] = Leader
           /\ nextIndex \in Index
           /\ \E v \in Value: leaderLog' = [leaderLog EXCEPT ![currentTerm[i]][nextIndex] = <<currentTerm[i], v, FALSE>>]
           /\ UNCHANGED <<serverVars, log ,vote, msgsVars, negMsgs>>

Next == \/ \E i \in Server: Restart(i)
        \/ \E i \in Server: Timeout(i)
        \/ \E i \in Server: ReceiveHighTerm(i)
        \/ \E i \in Server: RequestVote(i)
        \/ \E i \in Server : HandleRequestVoteRequest(i)
        \/ \E i \in Server : BecomeLeaderCandidate(i)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server : CommitEntry(i)
        \/ \E i \in Server : ClientRequest(i)
        \/ \E i,j \in Server : RequestCommit(i)
        \/ \E i \in Server : HandleRequestCommitRequest(i)
        \/ \E i,j \in Server : RequestSync(i)
        \/ \E i \in Server : HandleRequestSyncRequest(i)


=============================================================================
\* Modification History
\* Last modified Tue May 11 19:47:37 CST 2021 by Dell
\* Created Mon May 10 22:09:59 CST 2021 by Dell
