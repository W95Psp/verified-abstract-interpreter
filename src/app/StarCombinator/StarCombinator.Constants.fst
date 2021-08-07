module StarCombinator.Constants

open FStar.String

let lowerCaseCharList
	= ['A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z']
let upperCaseCharList
	= ['a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z']
let anyCaseCharList = lowerCaseCharList @ upperCaseCharList
let digitList
	= ['1';'2';'3';'4';'5';'6';'7';'8';'9';'0']
let isSpecialChar
	= ['~';'@';'#';'$';'%';'^';'?';'!';'+';'*';'<';'>';'\\';'/';'|';'&';'=';':';'"']
let isSpaceChar
	= ['\t'; ' ']
let isNewLine
	= ['\n'; '\r']
