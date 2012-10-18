
use "parPelican.sml";

datatype sort = intvar |intval |boolvar |boolval | program |unbound
fun cmps y (i,x) = (x = y);  (* Usage: findi (cmps id) arr, return SOME (ind,
  "id") if found or NONE if not *)

fun idlook y x = (let val (id,tp)=x in id = y end);

exception chkextendEnvErr;
exception allocateErr;
exception applyEnvErr;
exception chktypeErr;


fun emptyEnv() = let val env = nil:(string * sort) list in env end

 and chkextendnEnv(env,ide,sort) = 
  let val v = List.find (idlook ide) env
   in case v of
           SOME (id,v)  => ((ide,sort)::env) 
         | NONE  => ( (ide,sort)::env ) 
   end
   
 and chkextendEnv(env,ide,sort) = 
  let val v = List.find (idlook ide) env
   in case v of
           SOME (id,v)  => (print("variable:"^id^" has been declared!\n");raise
           chkextendEnvErr) 
         | NONE  => ( (ide,sort)::env ) 
   end
   

and chkapplyEnv(locenv,ide)=
  let val ts = List.find (idlook ide) locenv
  in case ts of 
          NONE => (unbound)
        | SOME (id, dv) =>  (dv)
  end

and chktype (ASTTP tp) = 
   if tp = "integer" then intvar
      else if tp = "boolean" then boolvar
         else (print "Unregnized declared type!\n"; raise chktypeErr)
