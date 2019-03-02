From RecoveryRefinement Require Import Examples.Logging.LogAPI.
From RecoveryRefinement Require Import ExMach.ExMachAPI.

Import ProcNotations.
Local Open Scope proc.

(* disk layout *)
Definition log_len := 0.
Definition log_idx i := 1 + i.

(* memory addresses *)
(* txn1 occupies two addresses *)
Definition txn1_start := 0.
(* txn2 occupies two addresses *)
Definition txn2_start := 2.
Definition state := 4.
Definition disk_lock := 5.
Definition state_lock := 6.

Inductive BufState :=
| Empty | Txn1 | Txn2
| Txn12 | Txn21
.

Definition enc_state (s:BufState) : nat.
  destruct s; [ exact 0 | exact 1 | exact 2 | exact 3 | exact 4 ].
Defined.

Definition dec_state (n:nat) : option BufState :=
  match n with
  | 0 => Some Empty
  | 1 => Some Txn1
  | 2 => Some Txn2
  | 3 => Some Txn12
  | 4 => Some Txn21
  | _ => None
  end.

Definition state_length (s:BufState) : nat :=
  match s with
  | Empty => 0
  | Txn1 => 1
  | Txn2 => 1
  | Txn12 => 1
  | Txn21 => 1
  end.

Theorem enc_dec_id s : dec_state (enc_state s) = Some s.
Proof.
  destruct s; reflexivity.
Qed.

Local Notation proc := (proc ExMach.Op).

Definition read_txn start_addr :=
  a <- read_mem start_addr;
  v1 <- read_mem a;
  v2 <- read_mem (1 + a);
  Ret (v1, v2).

Definition write_txn txn log_start_addr :=
  _ <- write_disk (log_idx log_start_addr) (fst txn);
  write_disk (log_idx (1 + log_start_addr)) (snd txn).

Definition write_mem_txn start_addr log_start_addr :=
  txn <- read_txn start_addr;
    write_txn txn log_start_addr.

Definition get_state :=
  s_n <- read_mem state;
    Ret (match dec_state s_n with
         | Some s => s
         | None => Empty (* impossible *)
         end).

Definition put_state s :=
  write_mem state (enc_state s).

Definition commit :=
  _ <- lock state_lock;
  _ <- lock disk_lock;
  s <- get_state;
  l <- read_disk log_len;
  (* TODO: hold state lock only enough to read, then use disk lock to prevent
  concurrent commit *)
  _ <- match s with
      | Empty => Ret tt
      | Txn1 => write_mem_txn txn1_start l
      | Txn2 => write_mem_txn txn2_start l
      | Txn12 => _ <- write_mem_txn txn1_start l; write_mem_txn txn2_start l
      | Txn21 => _ <- write_mem_txn txn2_start l; write_mem_txn txn1_start l
      end;
  _ <- write_disk log_len (l + state_length s);
  _ <- put_state Empty;
  _ <- unlock disk_lock;
  _ <- unlock state_lock;
  Ret tt.

Definition reserve_state s : option (BufState * nat) :=
  match s with
  | Empty => Some (Txn1, txn1_start)
  | Txn1 => Some (Txn12, txn2_start)
  | Txn2 => Some (Txn21, txn1_start)
  | _ => None (* in-memory log is full *)
  end.

(* try_reserve returns Some start if it manages to reserve the transaction whose
in-memory start address is start, and None otherwise *)
Definition try_reserve : proc (option nat) :=
  _ <- lock state_lock;
  s <- get_state;
  ret <- match reserve_state s with
        | Some (s', txn_start) =>
          _ <- put_state s';
            Ret (Some txn_start)
        | None => Ret None
        end;
  (* TODO: hold lock across reservation and txn *)
  _ <- unlock state_lock;
  Ret ret.

Definition reserve : proc nat :=
  Loop (fun _ =>
          reservation <- try_reserve;
            match reservation with
            | Some start => LoopRet start
            | None => Continue tt
            end) tt.

Definition append txn : proc unit :=
  start <- reserve;
  _ <- write_mem start (fst txn);
  _ <- write_mem (1 + start) (snd txn);
  Ret tt.

Definition get_log i : proc (option nat) :=
  _ <- lock disk_lock;
  l <- read_disk log_len;
  ret <- if lt_dec i l
        then v <- read_disk (log_idx i);
               Ret (Some v)
        else Ret None;
  _ <- unlock disk_lock;
  Ret ret.

Definition recv : proc unit := Ret tt.

Definition impl : LayerImpl ExMach.Op Log.Op :=
  {| compile_op T (op: Log.Op T) :=
       match op with
       | Log.Append txn => append txn
       | Log.Commit => commit
       | Log.GetLog i => get_log i
       end;
     recover := Seq_Cons (recv) (Seq_Nil); |}.
