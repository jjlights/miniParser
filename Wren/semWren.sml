(* Sematics Functions *)


use "parWren.sml";

datatype valType = valint of int | valbool of bool | consbool of bool | consint of int |unused | undefined |inttp | booltp  

val MAXSIZE = 20;

exception evalErr;
exception execErr;
exception meaningErr;
exception emptyStoErr;
exception updateStoErr;
exception elaborateErr;
exception readErr;
exception writeErr;
exception ifErr;


(* Definition and Initialization of environment and storage *)

exception allocateErr;
exception applyStoErr;
exception updateStoErr;
exception getInpErr;
exception putOutErr;



(* Same for all language *)
fun addop (valint p,valint q) = valint (p + q)
and subop (valint p,valint q) = valint (p - q)
and mulop (valint p,valint q) = valint (p * q)
and divop (valint p,valint q) = valint (p div q)
and negop (valint p) = valint (0 - p)
and andop (valbool p,valbool q) = valbool (p andalso q)
and orop (valbool p,valbool q) = valbool (p orelse q)
and notop (valbool p) = valbool (not p)
and ltop (valint p,valint q) = valbool (p < q)
and leop (valint p,valint q) = valbool (p <= q)
and eqop (valint p,valint q) = valbool (p = q)
  | eqop (valbool p,valbool q) = valbool (p = q)
and neqop (valint p,valint q) = valbool (p <> q)
  | neqop (valbool p,valbool q) = valbool (p <> q)
and gtop (valint p,valint q) = valbool (p > q)
and geop (valint p,valint q) = valbool (p >= q);

fun cmps y (i,x) = (x = y);  (* Usage: findi (cmps id) arr, return SOME (ind, "id") if found or NONE if not *)
fun initial (stosz) =
  let val stov = array(stosz,unused)
      val stoi = array(stosz,"xxxx")   (* dummy string for undeclared *)
      val intp = [valint(23),valint(91),valint(149),valint(0)]
      val outpt = nil:valType list
  in (stoi,stov,intp,outpt)
  end

and allocate(sto,id,ASTTP tp) =
   let val (stoi, stov,intp,outpt) = sto
       val v = findi (cmps unused) stov
   in if v=NONE then (print("Not enouth storage\n"); raise allocateErr)
      else 
           let val SOME (ind, t) = v 
           in case tp of
             "integer" => let val t = update(stoi,ind,id)
                              val t = update(stov,ind,inttp)
                          in (stoi,stov,intp,outpt)
                          end
             |"boolean" =>
                          let val t = update(stoi,ind,id)
                              val t = update(stov,ind,booltp)
                          in (stoi,stov,intp,outpt)
                          end
             | _ => (print("Not a supported declaration type\n"); raise allocateErr)
           end
   end

and updateSto(sto,id,ev) =
   let val (stoi,stov,intp,outpt) = sto
       val v = findi (cmps id) stoi
   in case v of
           SOME (ind,ide)  =>
                        let val  var=sub(stov,ind)
                        val t = update(stov,ind,ev)
                        in (stoi,stov,intp,outpt)
                        end
         (*| NONE => (print ("Undeclared variable!\n"); raise updateStoErr)*)
         | NONE => (raise updateStoErr)
   end

and applySto(sto,id) =
   let val (stoi, stov,intp,outpt) = sto
       val v = findi (cmps id) stoi
   in case v of
        SOME (ind, ide) =>  (sub(stov,ind)):valType
       | NONE => (raise applyStoErr)
       (* | NONE => (print ("Reference an undecleared variable!\n";raise
       * applyStoErr)) *)
   end

and getInp(sto) =
   let val (stoi, stov,intp,outpt) = sto
       val ev = hd(intp)
       val nint = rev(hd(intp)::rev(tl(intp)))
   in (ev, (stoi, stov, nint, outpt))
   end
   
and putOut(sto,ex) =
   let val (stoi, stov,intp,outpt) = sto
       val nout = ex::outpt 
   in (stoi,stov,intp,nout)
   end


fun eval (exp) sto =
  case exp of
    ASTNUM  ( p ) =>  (valint(p))
     |ASTBOOL  ( p ) =>  (valbool(p))
     | ASTID  ( p ) => 
                     let val dval = (applySto(sto,p))
                     in dval
                     (*
                     in case dval of 
                             undefined => (print "Reference an undefined variable!\n";raise evalErr)
                           | _   => dval
                           *)
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
                              valint 0  => (print ("Devided by Zero!\n"); raise evalErr)
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
                           end

and meaning (PROG (block) )  = let val emptysto = (initial(MAXSIZE)) in (perform block emptysto) end

and perform (DECLLST decls, CMDLST cmds) sto =
    let val sto1 = (elaborates decls sto) in (execs cmds sto1) end

and elaborates (nil) sto = sto
   | elaborates (decl::lst) sto = let val sto1 = (elaborate decl sto) in (elaborates lst sto1) end

and elaborate (decl) sto =
   case decl of 
      DECL (tp,id::lst)  =>
                           let val sto1 = allocate(sto,id,tp)
                           in (elaborate (DECL(tp,lst)) sto1)
                           end
      |DECL (tp,nil)  => (sto)

and execs nil sto = (sto)
  | execs (cmd::lst) sto =
  let val nsto = (exec (cmd) sto) in (execs lst nsto) end

and exec cmd sto =
  case cmd of
    ASTSKIP => sto
   |ASGN ( ide, exp ) =>  
                        let val ex = (eval exp sto)
                        in (updateSto( sto,ide, ex))
                        end      
     | ASTWHILE ( exp, cmds ) => 
                            let 
                              fun loop sto = 
                                  let val p = (eval exp sto) 
                                  in case p of
                                    valbool true => let val nsto = (execs cmds sto)  
                                                    in (loop nsto) 
                                                    end
                                    |valbool false => sto
                                    |_ => (print "Boolean result expected from expression!\n"; raise whileErr) 
                                  end
                            in (loop sto)
                            end
   | ASTIF2 ( exp, cmds ) => 
                           let val p = (eval exp sto)
                           in case p of
                              valbool true => (execs cmds sto)
                            | valbool false => sto
                            |_ => (print "Boolean result expected from expression!\n"; raise ifErr) 
                           end
   |  ASTIF1 ( exp, cmdst, cmdsf )  =>
                           let val p = (eval exp sto)
                           in case p of
                              valbool true => (execs cmdst sto)
                            | valbool false => (execs cmdsf sto)
                            |_ => (print "Boolean result expected from expression!\n"; raise ifErr) 
                           end
   | ASTREAD ( ide ) => let val (ev,sto1) = getInp(sto)     (* Also update the input list *)
                       in (updateSto(sto1,ide,ev))
                       end
                               (* else let val r = valOf(TextIO.inputLine * TextIO.stdIn) *)

   | ASTWRITE ( exp ) => let val ex = (eval exp sto)
                            val sto = putOut(sto,ex)
                        in (sto)
                        end

   | _ => (print "Unexpected command!\n"; raise execErr)

   (*
val tklst = mklst(lexer());
(*val t = printlist(parTKL(tklst));*)
val partr = parse_program(tklst);
val sto = meaning(partr);
*)
