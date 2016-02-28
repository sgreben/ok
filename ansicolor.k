\d c
red:"\033[31m"
green:"\033[32m"
yellow:"\033[33m"
blue:"\033[34m"
magenta:"\033[35m"
cyan:"\033[36m"
white:"\033[37m"
default:"\033[39m"
nth:{"\033[3",($x!10),"m"}
apply:{[c;x]c,x,default}
\d .k