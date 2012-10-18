
datatype valType = valint of int | valbool of bool | unbound | unused | undefined | inttp | booltp  
datatype dnType =  contc of ((string *valType) list * valType list -> (string *valType) list * valType list) |label of (astcmd list)

fun cmps y (i,x) = (x = y);  (* Usage: findi (cmps id) arr, return SOME (ind, "id") if found or NONE if not *)

fun idlook y x = (let val (id:string,tp)=x in id = y end);
fun left(ll,a) = 
               let val (id,t)=hd(ll) 
               in  if a=id then nil else if (List.null ll) then nil else (hd(ll))::left((tl(ll)),a)
               end
fun right(rl,a) = 
               let val (id,t)=hd(rl) 
               in if a=id then (tl(rl)) else if (List.null rl) then nil else right((tl(rl)),a)
               end

exception extendEnvErr;
exception allocateErr;
exception applyEnvErr;
exception applyStoErr;


fun emptyEnv() = let val env = nil:(string * dnType) list in env end

fun initial (stosz) =
  let val stov =nil:(string * valType) list
      val env = nil:(string * dnType) list
      val intp = [valint(23),valint(91),valint(149),valint(0)]
      val sto = (stov,intp)
      fun idenCont(sto) = (sto)
  in (env,idenCont,sto)
  end

(*
and extendEnv(env,nil,nil) = env
    | extendEnv(env,lb::lbl,dv::dvl) = extendEnv((lb,dv)::env,lbl,dvl)
    *)
   
and extendEnv(env,ide,dv) =
  let val v = List.find (idlook ide) env
   in case v of
           SOME (id,olddv)  => 
                          let val ll = left(env,id) 
                              val rl = right(env,id)
                          in (ll @ ((id,dv)::rl) )
                          end
         | NONE  => (print(ide^" is in extendEnv!\n"); (ide,dv)::env )
   end
   
and applyEnv(env,lb) =
  let val ts = List.find (idlook lb) env
  in case ts of 
          NONE => (print ("Reference an undecleared label:"^lb^"\n"); raise applyEnvErr)
        | SOME (id, dv) => 
                            (print("Reference an label:"^lb^"\n"); (dv) )
  end

and updateSto(sto,ide,sv) =
   let val (stov,intp) = sto
    val v = List.find (idlook ide) stov
   in case v of
           SOME (id,oldsv)  => 
                          let val ll = left(stov,id) 
                              val rl = right(stov,id)
                              val nsto =ll @ ((id,sv)::rl)
                          in (nsto,intp)
                          end
         | NONE  => ( ((ide,sv)::stov), intp )
   end
   
and applySto(sto,ide) =  
   let val (stov,intp) = sto
   val ts = List.find (idlook ide) stov
  in case ts of 
          NONE => (print "Reference an undecleared variable!\n"; raise applyStoErr)
        | SOME (id, sv) =>  (sv)
  end

and getInp(sto) =
   let val (stov,intp) = sto
       val ev = hd(intp)
       val nint = rev(hd(intp)::rev(tl(intp)))
   in (stov, nint)
   end
   

