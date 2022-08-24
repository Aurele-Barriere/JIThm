(* Interprteting the Intermediate Representation *)

Require Import common.
Require Import Integers.
Require Import Events.
Require Import IR.
Require Import monad.
Require Import primitives.
Require Import Errors.

Definition eval_reg (r:reg) (rm:reg_map) : res int :=
  try_op (PTree.get r rm) "Unassigned register".


Definition int_of_bool (b:bool) : int :=
  if b then Int.one else Int.zero.

(* matches the semantics of the Omod operation *)
Definition eval_mod (n1 n2:int) : res int :=
  if Int.eq n2 Int.zero || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
  then Error ((MSG "Undefined Modulo")::nil)
  else OK (Int.mods n1 n2).
  

Definition eval_expr (e:expr) (rm:reg_map): res int :=
  match e with
  | BIN b o1 o2 =>
    do v1 <- eval_reg o1 rm;
      do v2 <- eval_reg o2 rm;
      match b with
      | bplus => OK (Int.add v1 v2)
      | bneg => OK (Int.sub v1 v2)
      | bmul => OK (Int.mul v1 v2)
      | beq => OK (int_of_bool (Int.eq v1 v2))
      | blt => OK (int_of_bool (Int.lt v1 v2))
      | bmod => eval_mod v1 v2
      end
  | UNA u o1 =>
    do v <- eval_reg o1 rm;
      match u with
      | uneg => OK (Int.neg v)
      | ueqzero => OK (int_of_bool (Int.eq v Int.zero))
      | uplus i => OK (Int.add v i)
      | umul i => OK (Int.mul v i)
      end
  | ZAR z =>
    match z with
    | zconst i => OK i
    end
  end.

Fixpoint eval_list_reg (lr:list reg) (rm:reg_map): res (list int) :=
  match lr with
  | nil => OK nil
  | r::lr' => do v <- eval_reg r rm;
              do lv <- eval_list_reg lr' rm;
              OK (v::lv)
  end.

(* Might be deprecated since the Call expects a reg list, not an expr list *)
Fixpoint eval_list (le:list expr) (rm:reg_map): res (list int) :=
  match le with
  | nil => OK nil
  | ex::le' => do v <- eval_expr ex rm;
                 do lv <- eval_list le' rm;
                 OK (v::lv)
  end.

Fixpoint init_regs (valist:list int) (params:list reg): res reg_map :=
  match valist with
  | nil => match params with
           | nil => OK empty_regmap
           | _ => Error ((MSG "Not enough arguments")::nil)
           end
  | val::valist' => match params with
                   | nil => Error ((MSG "Too many arguments")::nil)
                   | par::params' => do rm' <- init_regs valist' params';
                                       OK (rm' # par <- val)
                    end
  end.

Definition bool_of_int (i:int) : bool :=
  match (Int.intval i) with
  | 0 => false
  | _ => true
  end.

(* Creating a new Register Mapping from a Varmap *)
Fixpoint update_regmap (vm:varmap) (rm:reg_map): res reg_map :=
  match vm with
  | nil => OK empty_regmap
  | (r,e)::vm' =>
    do v <- eval_expr e rm;
      do rm' <- update_regmap vm' rm;
      OK (rm' # r <- v)
  end.


Definition ir_int_step (is:ir_state) : free (trace * itret checkpoint ir_state) :=
  match is with
    (v, pc, rm) =>
    do i <<- try_option ((ver_code v) # pc) "No instruction to execute";
      match i with
      | Nop next =>
        fret (E0, Halt (v, next, rm))

      | IPrint r next =>
        do res <<- fret' (eval_reg r rm);
          fret (print_event res, Halt (v, next, rm))
        
      | Op r ex next =>
        do res <<- fret' (eval_expr ex rm);
          fret (E0, Halt (v, next, rm # r <- res))

      | Cond r tr fl =>
        do guard <<- fret' (eval_reg r rm);
          match (bool_of_int guard) with
          | true => fret (E0, Halt (v, tr, rm))
          | false => fret (E0, Halt (v, fl, rm))
          end

      | Call fid args retreg next =>
        do _ <<- fprim(Prim_PushIRSF (retreg, v, next, rm));
          do argvals <<- fret' (eval_list_reg args rm);
          fret (E0, Done (C_Call (ir_call fid argvals)))
              
      | Return retreg =>
        do retval <<- fret' (eval_reg retreg rm);
          fret (E0, Done (C_Return (ir_ret retval)))

      | MemSet adreg valreg next =>
        do ad <<- fret' (eval_reg adreg rm);
          do val <<- fret' (eval_reg valreg rm);
          do _ <<- fprim(Prim_MemSet ad val);
          fret (E0, Halt (v, next, rm))

      | MemGet dstreg adreg next =>
        do ad <<- fret' (eval_reg adreg rm);
          do res <<- fprim(Prim_MemGet ad);
          fret (E0, Halt (v, next, rm # dstreg <- res))
               
      | Assume r (ftgt, ltgt) vm next =>
        do guard <<- fret' (eval_reg r rm);
          match (bool_of_int guard) with
          | true => fret (E0, Halt (v, next, rm)) (* we pass the test, going to next label *)
          | false =>
            do newrm <<- fret' (update_regmap vm rm);
              fret (E0, Done (C_Deopt (ir_deopt ftgt ltgt newrm)))
          end
      end
  end.

Definition ir_step (is:ir_state) : free (trace * synchro_state) :=
  do (t,r) <<- ir_int_step is;
    fret (t,
        match r with
        | Halt is => Halt_IR is
        | Done cp => synchro_of cp
        end).

(* A fueled loop *)
(* deprecated. we only take single steps (fuel=1) in our JIT now to make the proof easier *)
Fixpoint ir_int_loop (is:ir_state) (fuel:nat) : free (trace * synchro_state) :=
  match fuel with
  | O => fret (E0, Halt_IR is)
  | Datatypes.S f =>
    do (t1, synchro) <<- ir_step is;
      match synchro with
      | Halt_IR is' => do (t2, is'') <<- ir_int_loop is' f;
                     fret (t1 ++ t2, is'')
      | S_Call _ => fret (t1, synchro)
      | S_Return _ => fret (t1, synchro)
      | S_Deopt _ => fret (t1, synchro)
      | EOE _ => fret (t1, synchro)
      | Halt_ASM _ _ => ferror (Errors.MSG "Unexpected ASM state"::nil)
      | Halt_RTL _ _ => ferror (Errors.MSG "Unexpected RTL state"::nil)
      | Halt_Block _ => ferror (Errors.MSG "Unexpected RTLblock state"::nil)
      end
  end.
