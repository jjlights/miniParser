(* Sematics Functions *)

use "flatGull.sml";
use "tableGull.sml";

exception evalErr;
exception execErr;
exception elaborateErr;
exception extendEnvsErr;
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

fun eval (exp) sto =
  case exp of
    ASTNUM  ( p ) =>  valint(p)
     | ASTBOOL  ( p ) =>  valbool(p)
     |ASTID  ( p ) => 
                     let val sv = applySto(sto,p)
                     in (sv)
                     end

     |ASTPLUS ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = addop(el,er)
                         in ex
                         end
     | ASTMINUS ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = subop(el,er)
                         in ex
                         end
     | ASTTIMES ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = mulop(el,er)
                         in ex
                         end
     | ASTDIV ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                        in case er of
                              valint 0  => (print ("Devided by Zero!\n"); raise
                                evalErr)
                              | _ => let val ex = divop(el,er)
                                     in ex
                                     end
                         end
     | ASTLESS ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = ltop(el,er)
                         in ex
                         end
     | ASTLESSEQ ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = leop(el,er)
                         in ex
                         end
     | ASTEQ ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = eqop(el,er)
                         in ex
                         end
     | ASTNEQ ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = neqop(el,er)
                         in ex
                         end
     | ASTGRTR ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = gtop(el,er)
                         in ex
                         end
     | ASTGRTREQ ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = geop(el,er)
                         in ex
                         end
     | ASTAND ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = andop(el,er)
                         in ex
                         end
     | ASTOR ( pl, pr) => let val el = (eval pl sto)
                             val er = (eval pr sto)
                             val ex = orop(el,er)
                         in ex
                         end
     | ASTNOT ( p )  =>  let val e = (eval p sto)
                             val ex = notop(e)
                         in ex
                         end
     | ASTNEG ( p )  =>  let val e = (eval p sto)
                             val ex = negop(e)
                         in ex
                         end
     | ASTPAREN ( p )  =>  let val ex = (eval p sto)
                           in ex
                           end;

val MAXSIZE = 20;

(*
fun getids(nil) = nil | getids(ASTLABEL(id,lst)::tr)= id::getids(tr)
fun getcmd(nil) = nil | getcmd(ASTLABEL(cmds,lst)::tr)= [lst]@getcmd(tr)
  *)

fun meaning (PROG (CMDLST(lblst))) = let val (emptyenv, idencont, emptysto) = initial(MAXSIZE)
in (perform lblst emptyenv idencont emptysto) end

and perform (lblst) env cont = 
   let val env1 = extendEnvs(env,lblst)
   in (execs lblst env1 cont)
   end
    
and extendEnvs (env,nil) = env
  | extendEnvs (env,(ASTLABEL(id,cmds))::lst)  =
          let val env1 = extendEnv(env,id,label(cmds)) 
           in extendEnvs(env1,lst)
           end
  | extendEnvs(env,_) = env

(*
and perform (lblst) env cont = 
  let val clst = 
                 let val newenv = extendEnvs(env,lblst,clst)
                 in (mkClist lblst newenv cont)
                 end 
  in (hd(clst))
  end

and extendEnvs (env,nil,nil) = env
  | extendEnvs (env,(ASTLABEL(id,cmds))::lst,cont::clist)  =
          let val env1 = extendEnv(env,id,contc(cont)) 
           in extendEnvs(env1,lst,clist)
           end
  | extendEnvs (env,_,_) = (print("Impossible!\n");raise extendEnvsErr)
  *)


and mkClist nil env cont = [cont]
    | mkClist (ASTLABEL(id,cmds)::lst) env cont =
    let val clst = (mkClist lst env cont)
        val cont1 = (execs cmds env (hd(clst)))
    in cont1::clst
    end

and execs nil env cont sto = (cont sto)
  | execs ((ASTLABEL(id,cmds))::lst) env cont sto = (execs cmds env cont sto)
  | execs ((ASTGOTO(id))::lst) env cont sto = let val label(cmds)=applyEnv(env,id) 
                       in (execs cmds env cont sto)
                       end
    | execs ((ASTIF1 ( exp, cmdst, cmdsf ))::lst) env cont sto = 
                           let val p = (eval exp sto)
                           in case p of
                              valbool true =>
                                          ( case cmdst of
                                               ASTLABEL (id, lst) :: tr => (perform lst env cont sto) 
                                               | (ASTGOTO(id))::lst   => let val label(cmds)=applyEnv(env,id) 
                                                                         in (execs cmds env cont sto)
                                                                           end
                                              |_ => let val ncont = (execs lst env cont) in (execs cmdst env cont sto) end
                                              )
                            | valbool false => (
                                           case cmdsf of
                                              ASTLABEL (id, lst) ::tr => (perform lst env cont sto) 
                                               | (ASTGOTO(id))::lst   => let val label(cmds)=applyEnv(env,id) 
                                                                         in (execs cmds env cont sto)
                                                                           end
                                              |_ => let val ncont = (execs lst env cont) in (execs cmdsf env cont sto) end
                                             )
                           end
  | execs (cmd::lst) env cont sto =
  let val ncont = (execs lst env cont) in (exec cmd env ncont sto) end

and exec cmd env cont sto =
  case cmd of
    ASTSKIP => (cont sto)
     |ASTSTOP => sto
(*     |ASTLABEL (id,cmds) =>  (execs cmds env cont sto) *)
(*     |ASTGOTO (id) =>  let val label(cmds)=applyEnv(env,id) 
                       in (execs cmds env cont sto)
                       end
                       *)
     | ASGN ( ide, exp ) =>  
                        let val ex = (eval exp sto)
                            val sto1 = updateSto(sto,ide,ex) 
                        in (cont sto1)  
                        end      
     | ASTWHILE ( exp, cmds ) => 
                            let 
                              fun loop env cont sto = 
                                  let val p = (eval exp sto)
                                  in case p of
                                    valbool true => let val ncont = (loop env cont)  
                                                    in case cmds of
                                                           ASTLABEL (id, lst)::tr => (perform cmds env ncont sto) 
                                                          |_ => (execs cmds env ncont sto)
                                                    end
                                    |valbool false => (cont sto)
                                    |_ => (print "Boolean result expected from expression!\n"; raise whileErr) 
                                  end
                            in (loop env cont sto)
                            end
    (*
    |ASTWRITE ( exp ) => 
                    let val ex = (eval exp env sto)
                        val sto1 = putOut(sto,ex)
                    in (print("Here in write!\n");sto1)
                    end
    | ASTDECLB block => (perform block env sto)

    | CALL ide  => 
                  let val proc0(proc) = applyEnv(env, ide)
                  in (proc sto)   
                  end
    |CALLPAR (ide, expl) =>
                  let val proc1(proc) = applyEnv(env, ide)
                      val (sto1, loc) = allocate sto
                  in (proc loc (updateSto(sto1,loc, eval (expl) env sto)) )    (* add expression list evaluate fun *) 
                  end

    |ASTREAD ( ide ) => 

    *)
   | _ => (print "Unexpected command!\n"; raise execErr)

val inf = TextIO.openIn "2.gull";
val lexer = makeLexer( fn n => valOf(inputLine( inf ) ));
fun mklst (END) = END::nil | mklst (v) = v::mklst(lexer());

val tklst = mklst(lexer());
val partr = parse_program(tklst);
val sto=meaning(go(partr));
