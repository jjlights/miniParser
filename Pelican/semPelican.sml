(* Semantics Functions *)

use "parPelican.sml";
use "tablePelican.sml";

exception evalErr;
exception execErr;
exception elaborateErr;
exception releaseErr;
exception meaningErr;
exception applyErr;
exception readErr;
exception writeErr;
exception ifErr;

fun addop (valint p,valint q) = valint (p + q);
fun subop (valint p,valint q) = valint (p - q);
fun mulop (valint p,valint q) = valint (p * q);
fun divop (valint p,valint q) = valint (p div q);
fun negop (valint p) = valint (0 - p);
fun andop (valbool p,valbool q) = valbool (p andalso q);
fun orop (valbool p,valbool q) = valbool (p orelse q);
fun notop (valbool p) = valbool (not p);
fun ltop (valint p,valint q) = valbool (p < q);
fun leop (valint p,valint q) = valbool (p <= q);
fun eqop (valint p,valint q) = valbool (p = q)
  | eqop (valbool p,valbool q) = valbool (p = q);
fun neqop (valint p,valint q) = valbool (p <> q)
  | neqop (valbool p,valbool q) = valbool (p <> q);
fun gtop (valint p,valint q) = valbool (p > q);
fun geop (valint p,valint q) = valbool (p >= q);

fun eval (exp) env sto =
  case exp of
    ASTNUM  ( p ) =>  valint(p)
     | ASTBOOL  ( p ) =>  valbool(p)
     |ASTID  ( p ) => 
                     let val dval = applyEnv(env,p)
                     in case dval of
                             consint v => valint(v)
                           | consbool v => valbool(v)
                           | varloc loc => if (applySto(sto,loc)) = undefined then
                                           (print "Reference an undefined variable!\n";raise evalErr)
                                        else let val str = Int.toString(loc)
                                        in (print("evaluate "^p^" at location "^str^"\n");(applySto(sto,loc)))
                                             end
                     end

     |ASTPLUS ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = addop(el,er)
                         in ex
                         end
     | ASTMINUS ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = subop(el,er)
                         in ex
                         end
     | ASTTIMES ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = mulop(el,er)
                         in ex
                         end
     | ASTDIV ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                        in case er of
                              valint 0  => (print ("Devided by Zero!\n"); raise
                                evalErr)
                              | _ => let val ex = divop(el,er)
                                     in ex
                                     end
                         end
     | ASTLESS ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = ltop(el,er)
                         in ex
                         end
     | ASTLESSEQ ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = leop(el,er)
                         in ex
                         end
     | ASTEQ ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = eqop(el,er)
                         in ex
                         end
     | ASTNEQ ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = neqop(el,er)
                         in ex
                         end
     | ASTGRTR ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = gtop(el,er)
                         in ex
                         end
     | ASTGRTREQ ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = geop(el,er)
                         in ex
                         end
     | ASTAND ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = andop(el,er)
                         in ex
                         end
     | ASTOR ( pl, pr) => let val el = (eval pl env sto)
                             val er = (eval pr env sto)
                             val ex = orop(el,er)
                         in ex
                         end
     | ASTNOT ( p )  =>  let val e = (eval p env sto)
                             val ex = notop(e)
                         in ex
                         end
     | ASTNEG ( p )  =>  let val e = (eval p env sto)
                             val ex = negop(e)
                         in ex
                         end
     | ASTPAREN ( p )  =>  let val ex = (eval p env sto)
                           in ex
                           end;


val MAXSIZE = 20;

(* Main Function *)

fun meaning (PROG (id,block)) = let val (emptyenv, emptysto) = initial(MAXSIZE)
in (perform block emptyenv emptysto) end

and perform (BLOCK (DECLLST decls, CMDLST cmds)) (env:((string*int*dnType)list *int)) sto = 
let  
    val env = incrScp(env);
    val (env1,sto1) = (elaborates decls env sto)
    val sto1 = (execs cmds env1 sto1)
    val sto2 = (releases decls env1 sto1)
in (sto2) end

and releases (nil) env sto = (sto)
   | releases (decl::lst) env sto =
      let val sto1 = (release decl env sto) 
      in (releases lst env sto1) end

and release (decl) env sto =
   case decl of 
      DECL (tp,lst)  =>
                           let fun del nil env sto = sto
                               | del (id::bar) env sto =
                                let val varloc(loc) = applyEnv(env,id) 
                                    val sto1 = deallocate(sto,loc)
                                in (del bar env sto1)
                                end
                           in (del lst env sto)
                           end
      | CONDECL (cons,exp) => sto
      | PROC (id, block) => sto
      |PROCPAR (id, parl, block) => sto
     
and elaborates (nil) env sto = (env, sto)
   | elaborates (decl::lst) env sto =
      let val (env1,sto1) = (elaborate decl env sto) in (elaborates lst env1 sto1) end

and vardecl (id,tp) env sto = 
   let val (sto1,loc) = (allocate sto)     (* allocate sto *)
   in (extendEnv(env,id, varloc(loc)),sto1)  (* extendEnv(env,id,var(loc)) *)
   end
   
and elaborate (decl) env sto =
   case decl of 
      DECL (tp,id::lst)  =>
                           let val (env1, sto1) = (vardecl (id,tp) env sto)
                           in (elaborate (DECL(tp,lst)) env1 sto1)
                           end
      | DECL (tp,nil)  => (env, sto)
      | CONDECL (cons,exp) => let val const = (eval exp env sto)
                              in case const of
                                    valint i  => ( extendEnv(env,cons, consint(i)), sto )
                                    |valbool i => ( extendEnv(env,cons, consbool(i)), sto )
                                    |_ => (print "Impossible!\n";raise elaborateErr)
                              end 
      |PROC (id, block) => 
                         let val env1 = extendEnv(env,id,codes(block))
                         in (env1, sto)
                         end
          (*
                         let val proc = (perform block env)
                             val dn = proc0(proc)
                         val env1 = extendEnv(env,id,dn)
                         in (env1,sto)
                         end
                         *)
     |PROCPAR (id, parl, block) => 
                               let val ASTPARL(lst) = parl
                                   val (par, tp)=hd(lst)
                                   val (env1, sto1) = (vardecl (par,tp) env sto)
                                   val env2 = extendEnv (env1, id, codespar(DECL(tp,[par]),block))
                         in (env2, sto)
                         end


and execs nil env sto = sto
  | execs (cmd::lst) env sto =
  let val nsto = (exec cmd env sto) in (execs lst env nsto) end

and exec cmd env sto =
  case cmd of
    ASTSKIP => sto
     | ASGN ( ide, exp ) =>  
                        let val ex = (eval (exp) env sto)
                          val varloc(loc) = (applyEnv(env, ide))   (* applyEnv *) in (updateSto(sto,loc,ex) )  (* updateSto *)
                                           end 
     | ASTWHILE ( exp, cmds ) => 
                            let 
                              fun loop env sto = 
                                  let val p = eval (exp) env sto 
                                  in case p of
                                    valbool true => let val nsto = execs (cmds) env sto  
                                                    in (loop env nsto) 
                                                    end
                                    |valbool false => sto
                                    |_ => (print "Boolean result expected from expression!\n"; raise whileErr) 
                                  end
                            in (loop env sto)
                            end
    | ASTIF2 ( exp, cmds ) => 
                           let val p = (eval exp env sto)
                           in case p of
                              valbool true => (execs cmds env sto)
                            | valbool false => sto
                            |_ => (print "Boolean result expected from expression!\n"; raise ifErr) 
                           end
    | ASTIF1 ( exp, cmdst, cmdsf )  =>
                           let val p = (eval exp env sto)
                           in case p of
                              valbool true => (execs cmdst env sto)
                            | valbool false => (execs cmdsf env sto)
                            |_ => (print "Boolean result expected from expression!\n"; raise ifErr) 
                           end
    | ASTDECLB block => 
                       (perform block env sto)
    | CALL ide  => 
                   let val codes(block) = applyEnv(env,ide)
                   in (perform block env sto)
                   end
        (*
                  let val proc0(proc) = applyEnv(env, ide)
                  in (proc sto)   
                  end
                  *)
      | CALLPAR (ide, expl) =>
                  let val codespar(par,block) = applyEnv(env, ide)
                     val BLOCK(DECLLST(decls),CMDLST(cmds)) = block
                     val DECL(tp,parl) = par
                    val ex = eval (hd(expl)) env sto
                  in case ex of 
                    valint v => let val block1 = BLOCK(DECLLST(par::decls),CMDLST(ASGN(hd(parl),ASTNUM(v))::cmds))
                         in (perform block1 env sto )    (* add expression list evaluate fun *) 
                         end
                   | valbool v =>        let val valbool(v)=ex
                          val block1 = BLOCK(DECLLST(par::decls),CMDLST(ASGN(hd(parl),ASTBOOL(v))::cmds))
                          in (perform block1 env sto )    (* add expression list evaluate fun *) 
                          end
                   |_ => (raise execErr)
                  end

    (*
    ASTREAD ( ide ) => 

    *)
    |ASTWRITE ( exp ) => 
                    let val ex = (eval exp env sto)
                        val sto1 = putOut(sto,ex)
                    in (print("Here in write!\n");sto1)
                    end

   | _ => (print "Unexpected command!\n"; raise execErr)


val inf = TextIO.openIn "trace2.pelican";
val lexer = makeLexer( fn n => valOf(inputLine( inf ) ));
fun mklst (END) = END::nil | mklst (v) = v::mklst(lexer());

val tklst = mklst(lexer());
val partr = parse_program(tklst); 
val sto = meaning(partr);
