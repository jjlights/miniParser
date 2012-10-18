(* Flat Labels *)

use "parGull.sml";

exception deepErr;
exception fdlbErr;
exception rmrdErr;

fun go (PROG (CMDLST cmds)) = 
let val flatcmds = flatten(cmds)
in (PROG(CMDLST(flatcmds)))
end

and scanlb (nil) = false
  | scanlb (cmd::cmds) =
case cmd of
      ASTLABEL (id,t) => true
   |_ =>scanlb(cmds)


and flatten (nil) = nil
  | flatten (cmds) = 
  let val f = scanlb(cmds)
  in if f=true then let val ft = flat(cmds)
                        val ftn = ASTLABEL("main",cmds)::ft
                    in  (rmrd(ftn))
                    end
  else deep(cmds)
  end

and flat(nil) = nil
  | flat(cmds) =
      let val (id,lb) = fdlb(cmds)
        val tr = flat(lb)
      in case lb of
              nil => tr
            |_  => (ASTLABEL(id,lb))::tr

      end

and fdlb(nil)=("empty",nil)
  | fdlb(cmd::lst)=
  case cmd of
  ASTLABEL (id,t) => (id,lst)
     |ASTSKIP => fdlb(lst)
     | ASGN ( ide, exp ) =>  fdlb(lst)
     | ASTWHILE ( exp, cmds ) => let val (a,b) = fdlb(cmds)
                                  in if b=nil then (fdlb(lst))
                                     else (a,b)
                                 end
    | ASTIF1 ( exp, cmdst, cmdsf )  => let val (a,b) = fdlb(cmdst)
                                       in if b=nil then let val (a,b)=fdlb(cmdsf)
                                                         in if b=nil then fdlb(lst)
                                                            else (a,b)
                                                        end
                                                            else (a,b)
                                       end
    |ASTREAD ( ide ) => fdlb(lst)
    |ASTWRITE ( exp ) =>  fdlb(lst)
    |ASTGOTO (id ) =>  fdlb(lst)
    |_ => (print"Not handle yet!\n";raise fdlbErr)

and deep(nil) = nil
  | deep(cmd::lst) =
  case cmd of
    ASTSKIP => cmd::(flatten(lst))
     | ASGN ( ide, exp ) =>  cmd::(flatten(lst))
     | ASTWHILE ( exp, cmds ) => (ASTWHILE(exp,flatten(cmds)))::(flatten(lst))
    | ASTIF1 ( exp, cmdst, cmdsf )  => let val t = flatten(cmdst)
                                           val f = flatten(cmdsf)
                                       in (ASTIF1(exp,t,f))::(flatten(lst))
                                       end
     |ASTREAD ( ide ) => cmd::(flatten(lst))
    |ASTWRITE ( exp ) =>  cmd::(flatten(lst))
    |ASTGOTO ( id ) =>  cmd::(flatten(lst))
    |_ => (print"Not handle yet!\n";raise deepErr)

and rmrd(nil) = nil
  | rmrd(cmd::lst) =
  case cmd of
     ASTLABEL (id,cmds) => if cmds=nil then rmrd(lst)
                           else (ASTLABEL(id,rmrd(cmds)))::(rmrd(lst))
     |ASTSKIP => cmd::(rmrd(lst))
     | ASGN ( ide, exp ) =>  cmd::(rmrd(lst))
     | ASTWHILE ( exp, cmds ) => (ASTWHILE(exp,rmrd(cmds)))::(rmrd(lst))
    | ASTIF1 ( exp, cmdst, cmdsf )  => let val t = rmrd(cmdst)
                                           val f = rmrd(cmdsf)
                                       in (ASTIF1(exp,t,f))::(rmrd(lst))
                                       end
     |ASTREAD ( ide ) => cmd::(rmrd(lst))
    |ASTWRITE ( exp ) =>  cmd::(rmrd(lst))
    |ASTGOTO ( id ) =>  cmd::(rmrd(lst))
    |_ => (print"Not handle yet!\n";raise rmrdErr)

        (*
    | ASTDECLB block => (perform block env sto)
    | CALL ide  => 
        |CALLPAR (ide, expl) =>
            *)

