theory KVS_WAL_ordered_disk
imports Main Option String
begin

(* We model the disk as list of strings. In this preliminary version, we assume a string can be contained in disk slot (ie., a block) *)
type_synonym disk = "string list" 

(* Convenience type which models a list of disk states that could result as an operation on the disk*)
type_synonym disk_states = "disk list"

(* Usually, the log is a dedicated portion in the disk. In our model, we model it as a separate disk. This pair of data and log portions
make up the actual disk*)
record diskpair = data :: disk
                  log :: disk

(* Convenience type which models a list of diskpairs *)
type_synonym diskpairlist = "diskpair list"

(* Helper to enumerate disk lists *)
fun enumdisks :: "disk list list  => disk list"
where
  "enumdisks [] = []"
| "enumdisks (x#d1) = (x) @ enumdisks d1"

(* Helper to enumerate diskpair lists *)
fun enumdiskpairs :: "diskpair list list  => diskpair list"
where
  "enumdiskpairs [] = []"
| "enumdiskpairs (x#d1) = (x) @ enumdiskpairs d1"

(* Helper to check if a given element in present in a list *)
fun list_contains :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
"list_contains item [] = False" |
"list_contains item (first # others) = ((item = first) \<or> (list_contains item others))"

(* Log update : This function models how a key value pair is updated on the log *)
(* Param1: key :: string *)
(* Param2: value :: string *)
(* returns: all possible log states :: disk_states *)
(* There are 3 slots in the log. The first slot contains information about the log itself
   It can either contain 'N' which means there is a log update currently happening or 'C'
   which means the log update completed and it is safe to apply the update. Note: We assume
   the log is cleaned properly (without failures) after applying an update from the log.
*)
fun log_update :: "string \<Rightarrow> string \<Rightarrow> disk_states"
where
"log_update key value  = [
                          [[],[],[]][0:=''N''],
                          [[],[],[]][0:=''N'',(Suc 0):=key],
                          [[],[],[]][0:=''N'',(Suc 0):=key,(Suc (Suc 0)):=value],
                          [[],[],[]][0:=''C'',(Suc 0):=key,(Suc (Suc 0)):=value]
                         ]"


(* Log recovery : This function models how the log is recovered. *)
(* Param1: index_to_apply :: nat *)
(* Param2: data_portion :: disk *)
(* Param3: log_portion :: disk *)
(* returns: data_portion :: disk*)
(* Checks if the first slot in the log is 'C' which means the log update has completed properly.
   In that case, it applies the update to index_to_apply in the data portion. Note: Recovery itself 
   can crash. This is modelled by function recover_crash *)
fun recover :: "nat \<Rightarrow> disk \<Rightarrow> disk \<Rightarrow> disk"
where
"recover idx data_disk log_disk  = (if(log_disk!0 = ''C'')
                 then data_disk[idx := log_disk!1, (Suc idx) := log_disk!2] else data_disk)"

(* Log recovery(crashing version) : This function models how the log is recovered. *)
(* Param1: index_to_apply :: nat *)
(* Param2: data_portion :: disk *)
(* Param3: log_portion :: disk *)
(* returns nothing *)
(* Checks if the first slot in the log is 'C' which means the log update has completed properly.
   In that case, it applies the update to index_to_apply in the data portion and marks the first slot as 'D'.
   Otherwise does nothing *)
(* returns: all possible disk pairs that would result if the recovery crashes :: diskpairlist *)
fun recover_crash :: "nat \<Rightarrow> disk \<Rightarrow> disk \<Rightarrow> diskpairlist"
where
"recover_crash idx data_disk log_disk  = 
                 (if(log_disk!0 = ''C'')
                 then
                 [
                  (| data = data_disk, log = log_disk |),
                  (| data = data_disk[idx := log_disk!1],
                                   log = log_disk |),
                  (| data = data_disk[idx := log_disk!1, (Suc idx) := log_disk!2],
                                   log = log_disk |),
                  (| data = data_disk[idx := log_disk!1, (Suc idx) := log_disk!2],
                                   log = log_disk[0 := ''D''] |)
                 ]
                 else 
                 [
                  (| data = data_disk, log = log_disk |)
                 ]
                 )" 

(* Log checkpointing : This function models how the log is checkpointed. *)
(* Param1: index_to_apply :: nat *)
(* Param2: data_portion :: disk *)
(* Param3: log_portion :: disk *)
(* returns nothing *)
(* Same as recovery but called during normal operation and not after failures *)
(* returns: data_portion :: disk*)
fun checkpoint :: "nat \<Rightarrow> disk \<Rightarrow> disk \<Rightarrow> disk"
where
"checkpoint idx data_disk log_disk  =(if(log_disk!0 = ''C'')
                 then data_disk[idx := log_disk!1, (Suc idx) := log_disk!2] else data_disk)"

(* KV_Put : This function models how our toy key-value store PUT operation works. *)
(* Param1: key :: string *)
(* Param1: value :: string *)
(* Param1: data_portion :: disk *)
(* Param2: index_to_apply: nat *)
(* returns all possible disk states that could result on doing this PUT operation :: disk_states *)
fun kv_put :: "string \<Rightarrow> string \<Rightarrow> disk \<Rightarrow> nat \<Rightarrow> disk_states"
where
"kv_put k v current_disk idx= map (checkpoint idx current_disk) (log_update k v)"

(*Test code*)
value "log_update ''a'' ''b''"
value "enumdisks [ [[''1'',''2''],[''3'',''4''],[''5'',''6'']],  [[''7'',''8''],[''9'',''10''],[''11'',''12'']] ]"
value "enumdiskpairs (map (recover_crash 1 [''x'',''y'',''z'']) (log_update ''a'' ''b''))"
value "map (recover 1 [''x'',''y'',''z'']) (log_update ''a'' ''b'')"
value "map (recover 5 [''1'',''2'',''3'',''4'',''5'',''6'',''7'']) (log_update ''a'' ''b'')"
value "enumdiskpairs (map (recover_crash 5 [''1'',''2'',''3'',''4'',''5'',''6'',''7'']) (log_update ''a'' ''b''))"
(*End of test code*)

(* Assuming no crashes during recovery, prove that the logging mechanism can atomically update a key value pair
   on disk *)
theorem atomic_recovery_no_crash_theorem:
shows   "length d \<ge> 2 \<and> (Suc idx) < length d \<and> (list_contains after (map (recover idx d) (log_update s1 s2))) \<and> s1\<noteq>[] \<and> s2 \<noteq>[]
         \<Longrightarrow>
         after!idx=d!idx \<and> after!(Suc idx)=d!(Suc idx)
         \<or>
         after!idx=s1 \<and> after!(Suc idx)=s2"
apply(auto)
done

(* Assuming crashes during recovery, prove that the logging mechanism can atomically update a key value pair
   on disk *)
theorem atomic_recovery_crash_theorem:
shows   "length d \<ge> 2 \<and> (Suc idx) < length d  \<and> ( list_contains after (enumdiskpairs (map (recover_crash idx d) (log_update s1 s2) ) ) )  \<and> s1\<noteq>[] \<and> s2 \<noteq>[]
         \<Longrightarrow>
         (log after)!0=''D'' \<Longrightarrow> (data after)!idx=s1 \<and> (data after)!(Suc idx)=s2
         \<and>
         (log after)!0=''N'' \<Longrightarrow> (data after)!idx=d!idx \<and> (data after)!(Suc idx)=d!(Suc idx)"
apply(auto)
done

(* Atomic KV puts *)
theorem kv_put_atomic_theorem:
shows   "length d \<ge> 2 \<and> (Suc idx) < length d  \<and> (list_contains after (kv_put s1 s2 d idx)) \<and> s1\<noteq>[] \<and> s2 \<noteq>[]
         \<Longrightarrow>
         after!idx=d!idx \<and> after!(Suc idx)=d!(Suc idx)
         \<or>
         after!idx=s1 \<and> after!(Suc idx)=s2"
apply(auto)
done
