program tobinary is
var n,p : integer;
begin
read n; p := 2;
while p<=n do p := 2*p end while;
p := p/2;
while p>0 do
if n>= p then write 1; n := n-p
else write 0 end if;
p := p/2
end while
end
