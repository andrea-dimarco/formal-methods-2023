/* N-Queens
 * Place queens on the chess-board
 *  in a way that no queen can attack any other.
 * The solution will be an array on N values with the 
 *  'vertical' position of the queens.
 */

/* PROPERTIES */
ltl sol { <> !(Queens@sol) } /* the counterexample will be the solution */
ltl ns { <> (Queens@sol) }

/* DEFINE MACROS */
#define N 8 // number of queens


/* DEFINE  GLOBAL VARIABLES */
byte result[N];
bool a[N];      // row
bool b[(N*2)-1] // diagonal of type /
bool c[(N*2)-1] // diagonal of type \


/* UTILITY */
/**
 * Randomly chooses a number for the row.
 *  This is were the queen will be placed.
 */
inline Choose(row)
{
	row = 1;
	do
	:: (row < N) -> row++;
	:: break;
	od;
}

inline Write(i)
{
	atomic {
		printf("Queens: ");
		i = 0;
		do
		:: (i < N) -> printf("%d, ", result[i]);
		:: else -> break;
		od;
		printf("\n");
	}
}


/* PROCESSES */
active proctype Queens()
{
	byte col = 1;
	byte i = 0;
	byte row;
	do
	:: Choose(row);
		enda: !a[row-1];
		endb: !b[row+col-2];
		endc: !c[row-col+7];
			a[row-1] = true;
			b[row+col-2] = true;
			c[row-col+(N-1)] = true;
			result[col-1] = row;
			if
			:: (col >= N) -> break;
			:: else -> col++;
			fi;
	od;
	Write(i);
	sol: assert(false);
}