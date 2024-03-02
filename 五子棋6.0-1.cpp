//д����ǰ��
// �����㷨������ʾ��
// 1.������ʹ�õ���alpha-beta��֦�㷨�Ľ��װ汾PVS�㷨�����㷨�������£�
//   ���������У���Ҫ����������Principal Variation Search, PVS����һ�ָĽ����alpha-beta��֦�㷨�����ڲ�����������
//   ��PVS�У�ÿ���ڵ㶼��ִ�л��������Ե����������ж��Ƿ������в���У���ȷ����ǰ����Ƿ���Ҫ�������ֿ��ܵ���в���С�
//   ����������Ӯ�ñ�������в����ʱ���㷨���������п��ܵķ������ƶ���Ȼ�󣬶�����ЩǱ�ڵķ������ƶ����㷨�᳢��ÿһ����
//   �ٴζԶԷ���ҽ�����в�����������������û���ҵ����ֵĹ�������ô����Ϊ�ҵ�����Ч�ķ�����������ӵ���Ч�����ļ����С�
//   ���������������һ����ʤ����в���У���ô���Ǳ�ڵķ����Ͳ������á��㷨������������̣�ֱ���ҵ�һ�鹤���ķ������ƶ���
//   ����ȷ����λ���Ѿ���ʧ��
// 2.����ĿӦ����Zobrist��ֵ���������£�
//   ���������������Ϸ�У�Zobrist��ֵ���Ӧ����Ҫ�������Ż�����״̬�Ŀ��ټ�����洢��
//   ͨ��Ϊ�����ϵ�ÿһ�����ܵ�����λ�÷���һ��Ψһ���������ÿ�������ƶ�����ӵ�������ʱ��
//   ����ʹ��������������µ�ǰ����״̬�Ĺ�ϣֵ�������ϣֵ����Ϊ��ǰ����״̬��Ψһ��ʶ��
//   ���Կ��ٵش洢�ͼ��������������Ѿ����������������á��������������㷨�����ظ�������״̬ʱ��
//   ����ֱ��ʹ�ô洢�����������������Ҫ���¼��㣬�Ӷ�����������Ч�ʡ����⣬����Zobristɢ�е���ƣ�
//   ��ʹ�Ƿǳ����Ƶ�����״̬Ҳ��������ȫ��ͬ�Ĺ�ϣֵ�����������ײ�Ŀ����ԣ�ȷ���˹�ϣֵ��׼ȷ�Ժ���Ч�ԡ�
// һЩ��Ҫ�Ĺ��ܼ�飺
//1.Zobrist��ϣ��InitZobrist ����ͨ��RandULL������������zobrist���顣ÿ��ChessDown���ӻ�DelChessɾ������ʱ���������zobristKey���Ա���ټ����ͱȽ�����״̬��
//2.���ͱ�InitChessType������ʼ�����ͱ�patternTable����16λ��key��ÿ��λ����������һ�����״̬������ɫ����LineType�����������͡�
//3.�߷����۱�InitChessType������moveEvaluateTable�������ĸ������ϵ�������GetMoveValue���������߷���
//4.���͸�����Ϊ�˿����ж����ͣ�ʹ��ChessTypeAssistance��������typeAssistanceTable����������ڿ��ٲ��Ҹ������ȡ����˳��ȡ��������������赲�������͡�
//5.���Ӻͻ��ݣ�ChessDown��DelChess������������������ӻ�ɾ�����ӣ�����������״̬��ÿ�β����������zobristKey��������UpdateType�����������͡�
//6.���͸��£�UpdateType��������ĳ������Χ����״̬��Ϊÿ���������GetKeyValue���ɼ�ֵ���룬����patternTable�в�����Ӧ�����͡�
//7.�߷�������GetMoveValue�������ݴ�����ĸ������ϵ����������߷��ļ�ֵ��
//8.ʤ����飺CheckWin����������һ�����Ƿ��������壬��ʤ��������
//9.SearchBest����Ҫ�����������������ҵ���ѵ�����λ�á���ʹ�õ��������������ԣ������ݵ�ǰ������״̬���Լ����ܵ��߷�����������ȷ������߷���
//10.RootSearch�������������������������ĸ��������߷�������������������������п��ܵ��߷�����ʹ��AlphaBeta����������ÿ���߷��ļ�ֵ��
//11.AlphaBeta��ʵ���˴�����Ҫ����������Principal Variation Search, PVS����alpha-beta��֦�����㷨������������ֲ���֦�����ܵķ�֧��
//12.evaluate�������������������ڼ��㵱ǰ����״̬�ķ�ֵ���������˸������ͶԵ�ǰ��ҵļ�ֵ���������һ��������ʾ�������Ե�ǰ��ҵ������̶ȡ�
//13.UpdateHash �� SearchHash���������������ڸ��ºͲ�ѯ�û�������һ�����ڼ����������������������������ݽṹ���Ա����ظ�������ͬ����֡�
//14.EvaluateMove���߷����ۺ��������ڸ������ϵĿ�λ��֣����ֻ��ڵ�ǰλ�����Ӻ�����γɵ����ͼ�ֵ��

#define _CRT_SECURE_NO_WARNINGS
#include<iostream>
#include<cstdlib>
#include<sstream>
#include<string>
#include<ctime>
#include<cstring>
#include<algorithm>

using namespace std;

// �����ν��б��
#define FIVE 7					// ����
#define LIVEFOUR 6				// ����
#define RUSHFOUR 5				// ����
#define LIVETHREE 4				// ����
#define SLEEPTHREE 3			// ����
#define LIVETWO 2				// ���
#define SLEEPTWO 1				// �߶�
// һЩ�����Ķ���
const int BOARDSIZE = 12;           // ���̳ߴ�
const int MAXSIZE = 20;				// �������ߴ�
const int MAXMOVES = 40;            // ÿ������֧��
const int HASHSIZE = 4194304;       // ��ϣ��ߴ�
const int PVSSIZE = 1048576;        // pvs�û���ߴ�
const int MAXDEPTH = 20;            // ����������
const int MINDEPTH = 2;			    // ������С���
// hash�����
const int HASH_EXACT = 0;
const int HASH_ALPHA = 1;
const int HASH_BETA = 2;
const int UNCERTAIN = -20000;
// ��������
const int X[4] = { 1, 0, 1, 1 };
const int Y[4] = { 0, 1, 1, -1 };
// �޷��ų������α���
typedef unsigned long long ULL;
// ���״̬
enum Pieces
{
	White = 0,
	Black = 1,
	Empty = 2,
	Out = 3
};
// ����
struct Pos
{
	int row;
	int col;
};
// �������ĵ�
struct Point
{
	Pos pos;
	int value;
};
// ���̵���ṹ
struct OnePoint
{
	int color;					//������ɫ
	int numInTwoBlocks;			//��������������
	int pattern[2][4];	        //�ڰ�˫���ĸ��������������
};
// Hash��ṹ
struct Hash
{
	ULL key;
	int depth;
	int hashtype;
	int value;
};
// Hash����Ҫ�����Ľṹ
struct PrincipalVariatio
{
	ULL key;
	Pos best;
};
// �߷�·��
struct MoveLine
{
	int n;
	Pos moves[MAXDEPTH];
};
struct MoveList
{
	int sign, n, index;
	bool isFirst;
	Pos hashMove;
	Pos moves[64];
};

class Board
{
public:
	int chessCount = 0;                           // ����������
	int size = 15;                                // ���̵�ǰ�ߴ�
	int board_start, board_end;                   // ����������Сֵ�����ֵ
	ULL zobristKey = 0;                           // ��ʾ��ǰ�����zobristKey
	ULL zobristBoard[2][MAXSIZE + 4][MAXSIZE + 4];// zobrist��ֵ��
	Hash hashTable[HASHSIZE];                     // ��ϣ��
	PrincipalVariatio pvsTable[PVSSIZE];          // pvs�û���
	int typeAssistanceTable[10][6][6][3];         // �����жϸ�����
	int patternTable[65536][2];                   // ���ͱ�
	int moveEvaluateTable[8][8][8][8];            // �߷����۱�
	OnePoint chess_map[MAXSIZE + 8][MAXSIZE + 8]; // ����
	Pos moveTypeList[MAXSIZE * MAXSIZE];          // �߷��б�
	Point tempMemList[256];                       // ��ʱ�洢�߷�
	bool mustLosePoint[MAXSIZE + 4][MAXSIZE + 4]; // ��¼���ڵ�ıذܵ�
	int player = Black;                           // ���ӷ�
	int enemy = White;                            // ���ַ�
	Point rootMove[64];                           // ���ڵ��߷�
	int rootMoveCount;                            // ���ڵ��߷�����
	int level = 0;                                // ��ǰ�����Ĳ���

	Board();
	~Board();
	void InitZobrist();
	// ��ʼ�����ͱ�
	void InitChessType();
	void SetSize();
	void ChessDown(Pos next);
	void DelChess();
	// ��������
	void UpdateType(int row, int col);
	ULL RandNum();
	// ��ȡ��λ�õ�key����  row,col : ����λ�õ�����  i : �ĸ�����
	int GetKeyValue(int row, int col, int i);
	// ��ȡ�߷��ļ�ֵ a,b,c,d : �ĸ����������
	int GetPval(int a, int b, int c, int d);
	// ��ȡ���� key : ��16λ,ÿ��λ�洢��λ�õ�״̬���ڡ��ס��ա�������  color : ��ʾҪ�ж���һ�������ͣ��ڻ��
	int LineType(int color, int key);
	int ShortLine(int* line);
	// �ж��ǻ�����������
	int CheckThreeType(int* line);
	// �ж��ǻ��Ļ�������
	int CheckFourType(int* line);
	// �������͸�����
	int ChessTypeAssistance(int len, int len2, int count, int block);
	// ���ص�count�������ɫ
	inline int color(int chessCount)
	{
		return chessCount & 1;
	}
	// �������x,y�Ƿ񳬳���Χ
	inline bool CheckXY(int row, int col)
	{
		return chess_map[row][col].color != Out;
	}
	// ������һ����ĵ���
	inline OnePoint* LastMove()
	{
		return &chess_map[moveTypeList[chessCount - 1].row][moveTypeList[chessCount - 1].col];
	}
	// color:����=1 ����=0 type:ͳ�����θ��������� c:���̸�λ�õ�ָ��
	inline void TypeCount(OnePoint* c, int color, int* type)
	{
		++type[c->pattern[color][0]];
		++type[c->pattern[color][1]];
		++type[c->pattern[color][2]];
		++type[c->pattern[color][3]];
	}
	// ���ص����Ƿ��������type
	inline bool IsType(OnePoint* c, int color, int type)
	{
		return c->pattern[color][0] == type || c->pattern[color][1] == type || c->pattern[color][2] == type || c->pattern[color][3] == type;
	}
	// �����һ�����Ƿ����
	inline bool CheckWin()
	{
		OnePoint* c = LastMove();
		return c->pattern[enemy][0] == FIVE || c->pattern[enemy][1] == FIVE || c->pattern[enemy][2] == FIVE || c->pattern[enemy][3] == FIVE;
	}
};
// ���캯����ȫ����ʼ��
Board::Board()
{
	InitChessType();
	InitZobrist();
	memset(chess_map, 0, sizeof(chess_map));
	memset(mustLosePoint, 0, sizeof(mustLosePoint));
	memset(moveTypeList, 0, sizeof(moveTypeList));
	memset(pvsTable, 0, sizeof(pvsTable));
	memset(hashTable, 0, sizeof(hashTable));
}
// ����������û��ʲô
Board::~Board()
{

}
// ������һ������Խ�ǿ�������
ULL Board::RandNum()
{
	return rand() ^ ((ULL)rand() << 15) ^ ((ULL)rand() << 30) ^ ((ULL)rand() << 45) ^ ((ULL)rand() << 60);
}
// ��ʼ��Zobrist��
void Board::InitZobrist()
{
	srand(time(NULL));
	for (int i = 0; i < MAXSIZE + 4; i++)
	{
		for (int j = 0; j < MAXSIZE + 4; j++)
		{
			zobristBoard[0][i][j] = RandNum();
			zobristBoard[1][i][j] = RandNum();
		}
	}
}
// �������̳ߴ�ͱ߽�
void Board::SetSize()
{
	size = BOARDSIZE;
	board_start = 4, board_end = size + 4;
	for (int i = 0; i < MAXSIZE + 8; i++)
	{
		for (int j = 0; j < MAXSIZE + 8; j++)
		{
			if (i < 4 || i >= size + 4 || j < 4 || j >= size + 4)
			{
				chess_map[i][j].color = Out;
			}
			else
			{
				chess_map[i][j].color = Empty;
			}
		}
	}
}
// ����
void Board::ChessDown(Pos next)
{
	int row = next.row;
	int col = next.col;

	level++;
	chess_map[row][col].color = player;
	zobristKey ^= zobristBoard[player][row][col];
	// �������巽
	player ^= 1;
	enemy ^= 1;

	moveTypeList[chessCount] = next;
	chessCount++;
	UpdateType(row, col);
	OnePoint* c = &chess_map[row][col];

	for (int i = row - 2; i <= row + 2; i++)
	{
		chess_map[i][col - 2].numInTwoBlocks++;
		chess_map[i][col - 1].numInTwoBlocks++;
		chess_map[i][col].numInTwoBlocks++;
		chess_map[i][col + 1].numInTwoBlocks++;
		chess_map[i][col + 2].numInTwoBlocks++;
	}
}
// ȡ������
void Board::DelChess()
{
	chessCount--;
	int row = moveTypeList[chessCount].row;
	int col = moveTypeList[chessCount].col;

	level--;
	player ^= 1;
	enemy ^= 1;
	zobristKey ^= zobristBoard[player][row][col];
	chess_map[row][col].color = Empty;
	UpdateType(row, col);
	OnePoint* c = &chess_map[row][col];

	for (int i = row - 2; i <= row + 2; i++)
	{
		chess_map[i][col - 2].numInTwoBlocks--;
		chess_map[i][col - 1].numInTwoBlocks--;
		chess_map[i][col].numInTwoBlocks--;
		chess_map[i][col + 1].numInTwoBlocks--;
		chess_map[i][col + 2].numInTwoBlocks--;
	}
}
// ��������
void Board::UpdateType(int row, int col)
{
	int a, b;
	int key;

	for (int i = 0; i < 4; ++i)
	{
		a = row + X[i];
		b = col + Y[i];
		for (int j = 0; j < 4 && CheckXY(a, b); a += X[i], b += Y[i], ++j)
		{
			key = GetKeyValue(a, b, i);
			chess_map[a][b].pattern[0][i] = patternTable[key][0];
			chess_map[a][b].pattern[1][i] = patternTable[key][1];
		}
		a = row - X[i];
		b = col - Y[i];
		for (int k = 0; k < 4 && CheckXY(a, b); a -= X[i], b -= Y[i], ++k)
		{
			key = GetKeyValue(a, b, i);
			chess_map[a][b].pattern[0][i] = patternTable[key][0];
			chess_map[a][b].pattern[1][i] = patternTable[key][1];
		}
	}
}
// ��ȡ��ֵ
int Board::GetKeyValue(int row, int col, int i)
{
	const int stepX = X[i];
	const int stepY = Y[i];
	int key = (chess_map[row - stepX * 4][col - stepY * 4].color)
		^ (chess_map[row - stepX * 3][col - stepY * 3].color << 2)
		^ (chess_map[row - stepX * 2][col - stepY * 2].color << 4)
		^ (chess_map[row - stepX * 1][col - stepY * 1].color << 6)
		^ (chess_map[row + stepX * 1][col + stepY * 1].color << 8)
		^ (chess_map[row + stepX * 2][col + stepY * 2].color << 10)
		^ (chess_map[row + stepX * 3][col + stepY * 3].color << 12)
		^ (chess_map[row + stepX * 4][col + stepY * 4].color << 14);
	return key;
}
// �ж�key���ͣ�������ͱ�
int Board::LineType(int color, int key)
{
	int line_left[9];
	int line_right[9];

	for (int i = 0; i < 9; i++)
	{
		if (i == 4)
		{
			line_left[i] = color;
			line_right[i] = color;
		}
		else
		{
			line_left[i] = key & 3;
			line_right[8 - i] = key & 3;
			key >>= 2;
		}
	}

	// ���������жϣ�Ȼ����������ж�
	int p1 = ShortLine(line_left);
	int p2 = ShortLine(line_right);

	// ��������������������п����ǻ���������
	if (p1 == SLEEPTHREE && p2 == SLEEPTHREE)
	{
		return CheckThreeType(line_left);
	}
	// ����������������ģ��п����ǻ��ģ�����
	else if (p1 == RUSHFOUR && p2 == RUSHFOUR)
	{
		return CheckFourType(line_left);
	}
	// ���ض���������Ǹ�
	else
	{
		return p1 > p2 ? p1 : p2;
	}
}
int Board::CheckThreeType(int* line)
{
	int color = line[4];
	int type;
	for (int i = 0; i < 9; i++)
	{
		if (line[i] == Empty)
		{
			line[i] = color;
			type = CheckFourType(line);
			line[i] = Empty;
			if (type == LIVEFOUR)
				return LIVETHREE;
		}
	}
	return SLEEPTHREE;
}
int Board::CheckFourType(int* line)
{
	int i, j, count;

	int five = 0;
	int color = line[4];
	for (i = 0; i < 9; i++)
	{
		if (line[i] == Empty)
		{
			count = 0;
			for (j = i - 1; j >= 0 && line[j] == color; j--)
				count++;
			for (j = i + 1; j <= 8 && line[j] == color; j++)
				count++;
			if (count >= 4)
				five++;
		}
	}
	// �����������λ���ܳ��壬���ǻ���
	return five >= 2 ? LIVEFOUR : RUSHFOUR;
}
// �ж�����
int Board::ShortLine(int* line)
{
	int empty = 0, block = 0;
	int len = 1, len_back = 1, count = 1;
	int k;

	int player = line[4];
	for (k = 5; k <= 8; k++)
	{
		if (line[k] == player)
		{
			if (empty + count > 4)
				break;
			++count;
			++len;
			len_back = empty + count;
		}
		else if (line[k] == Empty)
		{
			++len;
			++empty;
		}
		else
		{
			if (line[k - 1] == player)
			{
				block++;
			}
			break;
		}
	}
	// �����м�ո�
	empty = len_back - count;
	for (k = 3; k >= 0; k--)
	{
		if (line[k] == player)
		{
			if (empty + count > 4)
				break;
			++count;
			++len;
			len_back = empty + count;
		}
		else if (line[k] == Empty)
		{
			++len;
			++empty;
		}
		else
		{
			if (line[k + 1] == player)
			{
				block++;
			}
			break;
		}
	}
	return typeAssistanceTable[len][len_back][count][block];
}
int Board::ChessTypeAssistance(int len, int len_back, int count, int block)
{
	if (len >= 5 && count > 1)
	{
		if (count == 5)
		{
			return FIVE;
		}
		if (len > 5 && len_back < 5 && block == 0)
		{
			switch (count)
			{
				case 2:
					return LIVETWO;
				case 3:
					return LIVETHREE;
				case 4:
					return LIVEFOUR;
			}
		}
		else
		{
			switch (count)
			{
				case 2:
					return SLEEPTWO;
				case 3:
					return SLEEPTHREE;
				case 4:
					return RUSHFOUR;
			}
		}
	}
	return 0;
}
// ��ȡ��ֵ
int Board::GetPval(int a, int b, int c, int d)
{
	int type[8] = { 0 };
	type[a]++; type[b]++; type[c]++; type[d]++;

	if (type[FIVE] > 0)
		return 5000;
	if (type[LIVEFOUR] > 0 || type[RUSHFOUR] > 1)
		return 1200;
	if (type[RUSHFOUR] > 0 && type[LIVETHREE] > 0)
		return 1000;
	if (type[LIVETHREE] > 1)
		return 200;

	int value[6] = { 0, 2, 5, 5, 12, 12 };
	int score = 0;
	for (int i = 1; i <= RUSHFOUR; i++)
	{
		score += value[i] * type[i];
	}

	return score;
}
// ��ʼ����������
void Board::InitChessType()
{
	// ��ʼ�����͸�����
	for (int i = 0; i < 10; ++i)
	{
		for (int j = 0; j < 6; ++j)
		{
			for (int k = 0; k < 6; ++k)
			{
				for (int l = 0; l < 3; ++l)
				{
					typeAssistanceTable[i][j][k][l] = ChessTypeAssistance(i, j, k, l);
				}
			}
		}
	}
	//��ʼ�����ͱ�
	for (int key = 0; key < 65536; key++)
	{
		patternTable[key][0] = LineType(0, key);
		patternTable[key][1] = LineType(1, key);
	}
	//��ʼ���߷����۱�
	for (int i = 0; i < 8; ++i)
	{
		for (int j = 0; j < 8; ++j)
		{
			for (int k = 0; k < 8; ++k)
			{
				for (int l = 0; l < 8; ++l)
				{
					moveEvaluateTable[i][j][k][l] = GetPval(i, j, k, l);
				}
			}
		}
	}
}

class AI :public Board
{
private:
	// �������۷�ֵ
	int value[8] = { 0, 2, 12, 18, 96, 144, 800, 1200 };

public:
	int sumPosition = 0;			// ���������ξ�����
	int hashVisitCount = 0;			// hash����ʴ���
	int searchDepth = 0;			// ʵ���������
	int timeLeft = 90000;		    // һ�����ʣ��˼��ʱ��
	int eachThinkTime = 1200;		// ÿһ����˼��ʱ��
	int allThinkTime = 90000;	    // һ������˼��ʱ��
	int ThinkTime = 0;				// ��ǰ����˼��ʱ��
	Point bestPoint;				// AI˼������ѵ�
	MoveLine bestLine;			    // AI˼�������·��
	clock_t start, finish;			// AI��ʼ�ͽ���˼����ʱ���
	bool stopThink = false;			// AI�Ƿ�ֹͣ˼��

	// ������ѵ�
	Pos SearchBest();
	// ������ѵ�
	Pos BestMove();
	// ��������
	void SortInsert(Point* a, int n);
	// ����
	void SetChess(Pos next);
	// д���ϣ��
	void UpdateHash(int depth, int value, int hashtype);
	// ��¼pv�߷�
	void RecordPVMove(Pos best);
	// ��ȡ��һ���߷�
	Pos NextMove(MoveList& moveList);
	// ��ѯ��ϣ��
	int SearchHash(int depth, int alpha, int beta);
	// ���ص�ǰ���õ�����ʱ��
	int GetUsedTime();
	// ����ÿ�����õ�����ʱ��
	int EachSearchTime();
	// �����߷�
	int EvaluateMove(OnePoint* c);
	// �������ڵ�
	Point RootSearch(int depth, int alpha, int beta, MoveLine* pline);
	// ���ģ�Alpha-Beta��֦
	int AlphaBeta(int depth, int alpha, int beta, MoveLine* pline);
	// �ü��߷��б��ɹ����زü�����������޷��ü�����0
	int CutMoveList(Pos* move, Point* tempMemList, int Csize);
	// ���ɿ����߷�
	int GenerateMove(Pos* move);
	// ���۵�ǰ����
	int Evaluate();

};
// ���ص�ǰ���õ�����ʱ��
int AI::GetUsedTime()
{
	return (double)(clock() - start) / CLOCKS_PER_SEC * 1000;
}
// ����ÿ�����õ�����ʱ��
int AI::EachSearchTime()
{
	return (eachThinkTime < timeLeft / 6) ? eachThinkTime : timeLeft / 6;
}
// ��ѯ��ϣ��
int AI::SearchHash(int depth, int alpha, int beta)
{
	Hash* p_hash = &hashTable[zobristKey & (HASHSIZE - 1)];
	if (p_hash->key == zobristKey)
	{
		if (p_hash->depth >= depth)
		{
			if (p_hash->hashtype == HASH_EXACT)
			{
				return p_hash->value;
			}
			else if (p_hash->hashtype == HASH_ALPHA && p_hash->value <= alpha)
			{
				return p_hash->value;
			}
			else if (p_hash->hashtype == HASH_BETA && p_hash->value >= beta)
			{
				return p_hash->value;
			}
		}
	}
	return UNCERTAIN;
}
// д���ϣ��
void AI::UpdateHash(int depth, int value, int hashtype)
{
	Hash* p_hash = &hashTable[zobristKey & (HASHSIZE - 1)];
	p_hash->key = zobristKey;
	p_hash->value = value;
	p_hash->hashtype = hashtype;
	p_hash->depth = depth;
}
// ��������
void AI::SetChess(Pos next)
{
	next.row += 4, next.col += 4;
	ChessDown(next);
}
// ������ѵ�
Pos AI::BestMove()
{
	Pos best = SearchBest();
	best.row -= 4, best.col -= 4;
	return best;
}
// ������ѵ�
Pos AI::SearchBest()
{
	start = clock();
	sumPosition = 0;
	hashVisitCount = 0;

	Pos bestMove;
	// ��һ�������ĵ�
	if (chessCount == 0)
	{
		bestMove.row = size / 2 + 4;
		bestMove.col = size / 2 + 4;
		return bestMove;
	}
	// �ڶ������ѡ���һ������Χһ���ڵĵ�, ���������ѡ���һ������Χ�����ڵĵ�
	if (chessCount == 1 || chessCount == 2)
	{
		int rx, ry;
		srand(time(NULL));
		do
		{
			rx = moveTypeList[0].row + rand() % (chessCount * 2 + 1) - chessCount;
			ry = moveTypeList[0].col + rand() % (chessCount * 2 + 1) - chessCount;
		} while (!CheckXY(rx, ry) || chess_map[rx][ry].color != Empty);
		bestMove.row = rx;
		bestMove.col = ry;
		return bestMove;
	}
	// ������������
	stopThink = false;
	bestPoint.value = 0;
	level = 0;
	memset(mustLosePoint, false, sizeof(mustLosePoint));
	for (int i = MINDEPTH; i <= MAXDEPTH && !stopThink; i += 2)
	{
		searchDepth = i;
		bestPoint = RootSearch(searchDepth, -10001, 10000, &bestLine);
		if (stopThink || (searchDepth >= 10 && GetUsedTime() >= 1000 && GetUsedTime() * 12 > EachSearchTime()))
		{
			break;
		}
	}
	ThinkTime = GetUsedTime();
	bestMove = bestPoint.pos;

	return bestMove;
}
// �������ڵ�
Point AI::RootSearch(int depth, int alpha, int beta, MoveLine* pline)
{
	Point best = rootMove[0];
	MoveLine line;

	if (depth == MINDEPTH)
	{
		Pos moves[64];
		rootMoveCount = GenerateMove(moves);
		// ֻ����һ�������ŷ���ֱ�ӷ���
		if (rootMoveCount == 1)
		{
			stopThink = true;
			best.pos = moves[0];
			best.value = 0;
			pline->n = 0;
			return best;
		}

		for (int i = 0; i < rootMoveCount; i++)
		{
			rootMove[i].pos = moves[i];
		}
	}
	else
	{
		for (int i = 1; i < rootMoveCount; i++)
		{
			if (rootMove[i].value > rootMove[0].value)
			{
				Point temp = rootMove[0];
				rootMove[0] = rootMove[i];
				rootMove[i] = temp;
			}
		}
	}

	// ������ѡ��
	int value;
	for (int i = 0; i < rootMoveCount; i++)
	{
		// �����Ǳذܵ�
		Pos pos = rootMove[i].pos;
		if (!mustLosePoint[pos.row][pos.col])
		{
			line.n = 0;
			ChessDown(pos);
			do
			{
				if (i > 0 && alpha + 1 < beta)
				{
					value = -AlphaBeta(depth - 1, -alpha - 1, -alpha, &line);
					if (value <= alpha || value >= beta)
					{
						break;
					}
				}
				value = -AlphaBeta(depth - 1, -beta, -alpha, &line);
			} while (0);
			DelChess();

			rootMove[i].value = value;

			if (stopThink) break;

			if (value == -10000) mustLosePoint[pos.row][pos.col] = true;


			if (value > alpha)
			{
				alpha = value;
				best.pos = pos;
				best.value = value;
				// ����·��
				pline->moves[0] = pos;
				memcpy(pline->moves + 1, line.moves, line.n * sizeof(Pos));
				pline->n = line.n + 1;
				// �ҵ���ʤ��ֱ�ӷ���
				if (value == 10000)
				{
					stopThink = true;
					return best;
				}
			}
		}
	}


	return best;
}
// ��ȡ��һ���߷�
Pos AI::NextMove(MoveList& moveList)
{
	/*sign0:��ϣ���߷�
	 *sign1:����ȫ���߷�
	 *sign2:���η���sign1�е��߷�
	*/

	switch (moveList.sign)
	{
		case 0:
			moveList.sign = 1;
			PrincipalVariatio* e;
			e = &pvsTable[zobristKey % PVSSIZE];
			if (e->key == zobristKey)
			{
				moveList.hashMove = e->best;
				return e->best;
			}
		case 1:
			moveList.sign = 2;
			moveList.n = GenerateMove(moveList.moves);
			moveList.index = 0;
			if (moveList.isFirst == false)
			{
				for (int i = 0; i < moveList.n; i++)
				{
					if (moveList.moves[i].row == moveList.hashMove.row && moveList.moves[i].col == moveList.hashMove.col)
					{
						for (int j = i + 1; j < moveList.n; j++)
						{
							moveList.moves[j - 1] = moveList.moves[j];
						}
						moveList.n--;
						break;
					}
				}
			}
		case 2:
			if (moveList.index < moveList.n)
			{
				moveList.index++;
				return moveList.moves[moveList.index - 1];
			}
		default:
			Pos pos = { -1, -1 };
			return pos;

	}
}
// ��¼pv�߷�
void AI::RecordPVMove(Pos best)
{
	PrincipalVariatio* e = &pvsTable[zobristKey % PVSSIZE];
	e->key = zobristKey;
	e->best = best;
}
// Alpha-Beta��֦�㷨
int AI::AlphaBeta(int depth, int alpha, int beta, MoveLine* pline)
{
	sumPosition++;

	static int cnt = 1000;
	if (--cnt <= 0)
	{
		cnt = 1000;
		if (GetUsedTime() + 30 >= EachSearchTime())
		{
			stopThink = true;
			return alpha;
		}
	}
	//�Է��ѳ���
	if (CheckWin())
	{
		return -10000;
	}
	// Ҷ�ڵ�
	if (depth <= 0)
	{
		return Evaluate();
	}

	// ��ѯ��ϣ��
	int value = SearchHash(depth, alpha, beta);
	if (value != UNCERTAIN)
	{
		hashVisitCount++;
		return value;
	}

	MoveLine line;
	MoveList moveList;
	moveList.sign = 0;
	moveList.isFirst = true;
	Pos pos = NextMove(moveList);
	Point best = { pos, -10000 };
	int hashtype = HASH_ALPHA;
	while (pos.row != -1)
	{
		// ���֮ǰ�ڵ�·��
		line.n = 0;
		ChessDown(pos);
		do
		{
			if (!moveList.isFirst && alpha + 1 < beta)
			{
				value = -AlphaBeta(depth - 1, -alpha - 1, -alpha, &line);
				if (value <= alpha || value >= beta)
				{
					break;
				}
			}
			value = -AlphaBeta(depth - 1, -beta, -alpha, &line);
		} while (0);
		DelChess();

		if (stopThink)
			return best.value;

		if (value >= beta)
		{
			UpdateHash(depth, value, HASH_BETA);
			RecordPVMove(pos);
			return value;
		}
		if (value > best.value)
		{
			best.value = value;
			best.pos = pos;
			if (value > alpha)
			{
				hashtype = HASH_EXACT;
				alpha = value;
				pline->moves[0] = pos;
				memcpy(pline->moves + 1, line.moves, line.n * sizeof(Pos));
				pline->n = line.n + 1;
			}
		}
		pos = NextMove(moveList);
		moveList.isFirst = false;
	}


	UpdateHash(depth, best.value, hashtype);
	RecordPVMove(best.pos);

	return best.value;
}
// ���ͼ�֦
int AI::CutMoveList(Pos* move, Point* tempMemList, int candCount)
{
	//���ڻ��Ļ���������������Σ�ֱ�ӷ���
	if (tempMemList[0].value >= 2400)
	{
		move[0] = tempMemList[0].pos;
		return 1;
	}
	int moveCount = 0;
	//�Է�����
	if (tempMemList[0].value == 1200)
	{
		//Ѱ�ҶԷ��ܻ��ĵĵ�
		for (int i = 0; i < candCount; i++)
		{
			if (tempMemList[i].value == 1200)
			{
				move[moveCount] = tempMemList[i].pos;
				moveCount++;
			}
			else break;
		}
		//Ѱ��˫���ܳ��ĵĵ�
		for (int i = moveCount; i < candCount; ++i)
		{
			OnePoint* pos = &chess_map[tempMemList[i].pos.row][tempMemList[i].pos.col];
			if (IsType(pos, player, RUSHFOUR) || IsType(pos, enemy, RUSHFOUR))
			{
				move[moveCount] = tempMemList[i].pos;
				moveCount++;
				if (moveCount >= MAXMOVES)
				{
					break;
				}
			}
		}
	}
	return moveCount;
}
// �����߷�
int AI::GenerateMove(Pos* move)
{
	int candCount = 0;                //��ѡ�߷���
	int moveCount = 0;                //ɸѡ�������߷���
	int value;
	for (int i = board_start; i < board_end; i++)
	{
		for (int j = board_start; j < board_end; j++)
		{
			if (chess_map[i][j].numInTwoBlocks && chess_map[i][j].color == Empty)
			{
				value = EvaluateMove(&chess_map[i][j]);
				if (value > 0)
				{
					tempMemList[candCount].pos.row = i;
					tempMemList[candCount].pos.col = j;
					tempMemList[candCount].value = value;
					++candCount;
				}
			}
		}
	}
	// ����ֵ����
	SortInsert(tempMemList, candCount);
	moveCount = CutMoveList(move, tempMemList, candCount);
	// ���û�м�֦������ǰMaxMoves���߷�
	if (moveCount == 0)
	{
		for (int i = 0; i < candCount; i++)
		{
			move[i] = tempMemList[i].pos;
			moveCount++;
			if (moveCount >= MAXMOVES)
			{
				break;
			}
		}
	}

	return moveCount;
}
// ��������
void AI::SortInsert(Point* a, int n)
{
	int i, j;
	Point key;
	for (i = 1; i < n; i++)
	{
		key = a[i];
		for (j = i; j > 0 && a[j - 1].value < key.value; j--)
		{
			a[j] = a[j - 1];
		}
		a[j] = key;
	}
}
// �����ֵ
int AI::Evaluate()
{
	int playerType[8] = { 0 };               // ��¼���ӷ�������
	int enemyType[8] = { 0 };                // ��¼��һ��������
	int rushfour_temp = 0;			  	     // �����ϴ�ѭ���ҷ��ĳ��������������жϻ��ģ���������

	// ͳ���������ڵĿ�λ˫�������γɵ�����
	for (int i = board_start; i < board_end; ++i)
	{
		for (int j = board_start; j < board_end; ++j)
		{
			if (chess_map[i][j].numInTwoBlocks && chess_map[i][j].color == Empty)
			{
				rushfour_temp = playerType[RUSHFOUR];
				TypeCount(&chess_map[i][j], player, playerType);
				TypeCount(&chess_map[i][j], enemy, enemyType);
				//ͬһ�������������ģ��Ǿ��൱�ڻ���
				if (playerType[RUSHFOUR] - rushfour_temp >= 2)
				{
					playerType[RUSHFOUR] -= 2;
					playerType[LIVEFOUR]++;
				}
			}
		}
	}

	// ��ǰ�����ֵ���������
	// 1.�������ڳ����
	// 2.�Է�������������㣬�ذ�
	// 3.�Է����ܳ��壬�������ڻ���
	if (playerType[FIVE] >= 1) return 10000;
	if (enemyType[FIVE] >= 2) return -10000;
	if (enemyType[FIVE] == 0 && playerType[LIVEFOUR] >= 1) return 10000;

	int myScore = 0, enemyScore = 0;
	for (int i = 1; i < 8; ++i)
	{
		myScore += playerType[i] * value[i];
		enemyScore += enemyType[i] * value[i];
	}
	return myScore * 2 - enemyScore;
}
// �߷����
int AI::EvaluateMove(OnePoint* c)
{
	int score[2];
	score[player] = moveEvaluateTable[c->pattern[player][0]][c->pattern[player][1]][c->pattern[player][2]][c->pattern[player][3]];
	score[enemy] = moveEvaluateTable[c->pattern[enemy][0]][c->pattern[enemy][1]][c->pattern[enemy][2]][c->pattern[enemy][3]];

	if (score[player] >= 200 || score[enemy] >= 200)
	{
		return score[player] >= score[enemy] ? score[player] * 2 : score[enemy];
	}
	else
	{
		return score[player] * 2 + score[enemy];
	}
}

AI ai;
int i_playerColor = -1;
int main()
{
	char cmd[20];
	Pos input, best;
	ai.SetSize();
	Pos init_1, init_2, init_3, init_4, tmp;
	init_1.row = init_1.col = init_2.row = init_3.col = 5;
	init_4.row = init_4.col = init_2.col = init_3.row = 6;
	tmp.row = tmp.col = -1;
	while (scanf("%s", cmd) != EOF)
	{
		if (strcmp(cmd, "START") == 0)
		{
			scanf("%d", &i_playerColor);
			if (i_playerColor == 1)
			{
				ai.SetChess(init_2);
				ai.SetChess(init_1);
				ai.SetChess(init_3);
				ai.SetChess(init_4);
			}
			else if (i_playerColor == 2)
			{
				ai.SetChess(init_1);
				ai.SetChess(init_2);
				ai.SetChess(init_4);
				ai.SetChess(init_3);
				ai.SetChess(init_1);
			}
			printf("OK\n");
			fflush(stdout);
		}
		else if (strcmp(cmd, "PLACE") == 0)
		{
			scanf("%d %d", &input.row, &input.col);
			ai.SetChess(input);
		}
		else if (strcmp(cmd, "TURN") == 0)
		{
			best = ai.BestMove();
			ai.SetChess(best);
			printf("%d %d\n", best.row, best.col);
			fflush(stdout);
		}
		else if (strcmp(cmd, "END") == 0)
			break;
	}
	return 0;
}