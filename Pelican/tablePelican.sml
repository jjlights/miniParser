
open Array;

datatype valType = valint of int | valbool of bool | unbound | unused | undefined | inttp | booltp  
datatype dnType =  proc0 of ((valType array * valType list * valType list) ->
(valType array * valType list * valType list)) |consbool of bool | consint of
     int | varloc of int | codes of astblock | codespar of (astdecl*astblock)

fun cmps y (i,x) = (x = y);  (* Usage: findi (cmps id) arr, return SOME (ind, "id") if found or NONE if not *)

fun idlook y x = (let val (id:string,i:int,tp:dnType)=x in id = y end);
fun left(ll,a) = 
               let val (id,i,t)=hd(ll) 
               in  if a=id then nil else if (List.null ll) then nil else (hd(ll))::left((tl(ll)),a)
               end
fun right(rl,a) = 
               let val (id,i,t)=hd(rl) 
               in if a=id then (tl(rl)) else if (List.null rl) then nil else right((tl(rl)),a)
               end

exception extendEnvErr;
exception allocateErr;
exception applyEnvErr;
exception chkScpErr;

fun emptySto(stosz) = let val stov = array(stosz,unused) in stov end

fun emptyEnv() = let val env = nil:(string * dnType) list in env end

fun initial (stosz) =
  let val stov = array(stosz,unused)
      val env = nil:(string * int * dnType) list
      val scope = 0
      val intp = [valint(23),valint(91),valint(149),valint(0)]
      val outp = nil:valType list
  in ((env,scope),(stov,intp,outp))
  end

and extendEnv(env,ide,dv) =
  let val (envv,scp) = env
   val v = List.find (idlook ide) envv
   in case v of
           SOME (id,i,olddv)  => 
                          let val ll = left(envv,id) 
                              val rl = right(envv,id)
                          in if ide="b" then let val varloc(v)=dv
                                      in (print("extend "^ide^" in old with loc at"^(Int.toString(v))^"\n");((ll @ ((id,scp,dv)::rl) ),scp))
                                           end
                             else ((ll @ ((id,scp,dv)::rl) ),scp)
                          end
         | NONE  => (print("extend "^ide^" in new");(( (ide,scp,dv)::envv),scp))
   end
   
and applyEnv(env,ide) =
  let val (envv,scp) = env
   val ts = List.find (idlook ide) envv
  in case ts of 
          NONE => (print "Reference an undecleared variable!\n"; raise applyEnvErr)
        | SOME (id,i, dv) =>  (dv)
  end

and chkScp(env,ide) =
  let val (envv,scp) = env
   val v = List.find (idlook ide) envv
   in case v of
           SOME (id,i,olddv)  => if i=scp then true else false
         |NONE => (print("Impossible!\n");raise chkScpErr)
  end

and incrScp(env)= 
  let val (envv,scp) = env
  in (envv,scp+1)
  end
and decrScp(env)= 
  let val (envv,scp) = env
  in (envv,scp-1)
  end
and allocate(sto) =
  let val (stov,intp,outp) = sto
   val v = findi (cmps unused) stov
   in if v=NONE then (print("Not enouth storage\n"); raise allocateErr)
      else 
           let val SOME (loc, t) = v 
               val str = Int.toString(loc)
           in (print("New Location:"^str^"\n");
           (updateSto((stov,intp,outp),loc,undefined),loc))
           end
   end

and deallocate(sto,loc) =  (updateSto(sto,loc,unused))

and updateSto(sto,loc,ev) =
   let val (stov,intp,outp) = sto
    val t = update(stov,loc,ev)
   in (stov,intp,outp)
end

and applySto(sto,loc) =  
                    let val (stov,intp,outp) = sto
                    in  (sub(stov,loc)):valType
                    end

and getInp(sto) =
   let val (stov,intp,outp) = sto
       val ev = hd(intp)
       val nint = rev(hd(intp)::rev(tl(intp)))
   in (stov, nint, outp)
   end
   
and putOut(sto,ex) =
   let val (stov,intp,outp) = sto
       val nout = ex::outp
   in (stov,intp,nout)
   end

