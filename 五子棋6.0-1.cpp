//写在最前：
// 核心算法如下所示：
// 1.本代码使用的是alpha-beta剪枝算法的进阶版本PVS算法，该算法介绍如下：
//   在五子棋中，主要变异搜索（Principal Variation Search, PVS）是一种改进版的alpha-beta剪枝算法，用于博弈树搜索。
//   在PVS中，每个节点都会执行基于依赖性的搜索，以判断是否存在威胁序列，并确定当前玩家是否需要防御对手可能的威胁序列。
//   当搜索发现赢得比赛的威胁序列时，算法将返回所有可能的防御性移动。然后，对于这些潜在的防御性移动，算法会尝试每一个，
//   再次对对方玩家进行威胁搜索。如果重新搜索没有找到对手的攻击，那么就认为找到了有效的防御，将其添加到有效防御的集合中。
//   如果搜索发现了另一个获胜的威胁序列，那么这个潜在的防御就不起作用。算法将继续这个过程，直到找到一组工作的防御性移动，
//   或者确定该位置已经丢失。
// 2.本项目应用了Zobrist键值表，介绍如下：
//   在五子棋等棋类游戏中，Zobrist键值表的应用主要是用于优化棋盘状态的快速检索与存储。
//   通过为棋盘上的每一个可能的棋子位置分配一个唯一的随机数，每次棋子移动或添加到棋盘上时，
//   都会使用异或运算来更新当前棋盘状态的哈希值。这个哈希值将作为当前棋盘状态的唯一标识，
//   可以快速地存储和检索在搜索树中已经评估过的棋盘配置。这样，当搜索算法遇到重复的棋盘状态时，
//   可以直接使用存储的评估结果，而不需要重新计算，从而大大提高搜索效率。此外，由于Zobrist散列的设计，
//   即使是非常相似的棋盘状态也会生成完全不同的哈希值，这减少了碰撞的可能性，确保了哈希值的准确性和有效性。
// 一些重要的功能简介：
//1.Zobrist哈希：InitZobrist 函数通过RandULL生成随机数填充zobrist数组。每次ChessDown落子或DelChess删除棋子时，都会更新zobristKey，以便快速检索和比较棋盘状态。
//2.棋型表：InitChessType函数初始化棋型表，patternTable根据16位的key（每两位代表棋盘上一个点的状态）和颜色，用LineType函数评估棋型。
//3.走法评价表：InitChessType还生成moveEvaluateTable，根据四个方向上的棋型用GetMoveValue函数评价走法。
//4.棋型辅助表：为了快速判断棋型，使用ChessTypeAssistance函数生成typeAssistanceTable，这个表用于快速查找给定长度、后退长度、连续棋子数和阻挡数的棋型。
//5.走子和回溯：ChessDown和DelChess函数负责在棋盘上添加或删除棋子，并更新棋盘状态。每次操作都会更新zobristKey，并调用UpdateType函数更新棋型。
//6.棋型更新：UpdateType函数更新某个点周围棋型状态，为每个方向调用GetKeyValue生成键值编码，并在patternTable中查找相应的棋型。
//7.走法评估：GetMoveValue函数根据传入的四个方向上的棋型评估走法的价值。
//8.胜利检查：CheckWin函数检查最后一步棋是否导致了连五，即胜利条件。
//9.SearchBest：主要的搜索函数，用于找到最佳的落子位置。它使用迭代加深搜索策略，并根据当前的棋盘状态，以及可能的走法评估函数来确定最佳走法。
//10.RootSearch：根搜索函数，它在搜索树的根部进行走法的搜索和评估。它会遍历所有可能的走法，并使用AlphaBeta函数来评估每个走法的价值。
//11.AlphaBeta：实现了带有主要变异搜索（Principal Variation Search, PVS）的alpha-beta剪枝搜索算法，用于评估棋局并剪枝不可能的分支。
//12.evaluate：局面评估函数，用于计算当前棋盘状态的分值，它考虑了各种棋型对当前玩家的价值，并计算出一个分数表示这个局面对当前玩家的有利程度。
//13.UpdateHash 和 SearchHash：这两个方法用于更新和查询置换表，这是一种用于记忆搜索过程中棋局评估结果的数据结构，以避免重复评估相同的棋局。
//14.EvaluateMove：走法评价函数，用于给棋盘上的空位打分，评分基于当前位置落子后可能形成的棋型价值。

#define _CRT_SECURE_NO_WARNINGS
#include<iostream>
#include<cstdlib>
#include<sstream>
#include<string>
#include<ctime>
#include<cstring>
#include<algorithm>

using namespace std;

// 给棋形进行编号
#define FIVE 7					// 成五
#define LIVEFOUR 6				// 活四
#define RUSHFOUR 5				// 冲四
#define LIVETHREE 4				// 活四
#define SLEEPTHREE 3			// 眠三
#define LIVETWO 2				// 活二
#define SLEEPTWO 1				// 眠二
// 一些常量的定义
const int BOARDSIZE = 12;           // 棋盘尺寸
const int MAXSIZE = 20;				// 棋盘最大尺寸
const int MAXMOVES = 40;            // 每层最多分支数
const int HASHSIZE = 4194304;       // 哈希表尺寸
const int PVSSIZE = 1048576;        // pvs置换表尺寸
const int MAXDEPTH = 20;            // 搜索最大深度
const int MINDEPTH = 2;			    // 搜索最小深度
// hash表相关
const int HASH_EXACT = 0;
const int HASH_ALPHA = 1;
const int HASH_BETA = 2;
const int UNCERTAIN = -20000;
// 方向向量
const int X[4] = { 1, 0, 1, 1 };
const int Y[4] = { 0, 1, 1, -1 };
// 无符号长长整形别名
typedef unsigned long long ULL;
// 点的状态
enum Pieces
{
	White = 0,
	Black = 1,
	Empty = 2,
	Out = 3
};
// 坐标
struct Pos
{
	int row;
	int col;
};
// 带分数的点
struct Point
{
	Pos pos;
	int value;
};
// 棋盘单点结构
struct OnePoint
{
	int color;					//棋子颜色
	int numInTwoBlocks;			//两格内棋子数量
	int pattern[2][4];	        //黑白双方四个方向的棋型数据
};
// Hash表结构
struct Hash
{
	ULL key;
	int depth;
	int hashtype;
	int value;
};
// Hash表主要变例的结构
struct PrincipalVariatio
{
	ULL key;
	Pos best;
};
// 走法路线
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
	int chessCount = 0;                           // 棋盘落子数
	int size = 15;                                // 棋盘当前尺寸
	int board_start, board_end;                   // 棋盘坐标最小值和最大值
	ULL zobristKey = 0;                           // 表示当前局面的zobristKey
	ULL zobristBoard[2][MAXSIZE + 4][MAXSIZE + 4];// zobrist键值表
	Hash hashTable[HASHSIZE];                     // 哈希表
	PrincipalVariatio pvsTable[PVSSIZE];          // pvs置换表
	int typeAssistanceTable[10][6][6][3];         // 棋型判断辅助表
	int patternTable[65536][2];                   // 棋型表
	int moveEvaluateTable[8][8][8][8];            // 走法评价表
	OnePoint chess_map[MAXSIZE + 8][MAXSIZE + 8]; // 棋盘
	Pos moveTypeList[MAXSIZE * MAXSIZE];          // 走法列表
	Point tempMemList[256];                       // 临时存储走法
	bool mustLosePoint[MAXSIZE + 4][MAXSIZE + 4]; // 记录根节点的必败点
	int player = Black;                           // 下子方
	int enemy = White;                            // 对手方
	Point rootMove[64];                           // 根节点走法
	int rootMoveCount;                            // 根节点走法数量
	int level = 0;                                // 当前搜索的层数

	Board();
	~Board();
	void InitZobrist();
	// 初始化棋型表
	void InitChessType();
	void SetSize();
	void ChessDown(Pos next);
	void DelChess();
	// 更新棋型
	void UpdateType(int row, int col);
	ULL RandNum();
	// 获取该位置的key编码  row,col : 棋盘位置的坐标  i : 四个方向
	int GetKeyValue(int row, int col, int i);
	// 获取走法的价值 a,b,c,d : 四个方向的棋型
	int GetPval(int a, int b, int c, int d);
	// 获取棋型 key : 共16位,每两位存储该位置的状态：黑、白、空、棋盘外  color : 表示要判断哪一方的棋型：黑或白
	int LineType(int color, int key);
	int ShortLine(int* line);
	// 判断是活三还是眠三
	int CheckThreeType(int* line);
	// 判断是活四还是眠四
	int CheckFourType(int* line);
	// 生成棋型辅助表
	int ChessTypeAssistance(int len, int len2, int count, int block);
	// 返回第count步棋的颜色
	inline int color(int chessCount)
	{
		return chessCount & 1;
	}
	// 检查坐标x,y是否超出范围
	inline bool CheckXY(int row, int col)
	{
		return chess_map[row][col].color != Out;
	}
	// 返回上一步棋的单点
	inline OnePoint* LastMove()
	{
		return &chess_map[moveTypeList[chessCount - 1].row][moveTypeList[chessCount - 1].col];
	}
	// color:黑棋=1 白棋=0 type:统计棋形个数的数组 c:棋盘该位置的指针
	inline void TypeCount(OnePoint* c, int color, int* type)
	{
		++type[c->pattern[color][0]];
		++type[c->pattern[color][1]];
		++type[c->pattern[color][2]];
		++type[c->pattern[color][3]];
	}
	// 返回单点是否存在棋形type
	inline bool IsType(OnePoint* c, int color, int type)
	{
		return c->pattern[color][0] == type || c->pattern[color][1] == type || c->pattern[color][2] == type || c->pattern[color][3] == type;
	}
	// 检查上一步棋是否成五
	inline bool CheckWin()
	{
		OnePoint* c = LastMove();
		return c->pattern[enemy][0] == FIVE || c->pattern[enemy][1] == FIVE || c->pattern[enemy][2] == FIVE || c->pattern[enemy][3] == FIVE;
	}
};
// 构造函数，全部初始化
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
// 析构函数，没做什么
Board::~Board()
{

}
// 生成了一个随机性较强的随机数
ULL Board::RandNum()
{
	return rand() ^ ((ULL)rand() << 15) ^ ((ULL)rand() << 30) ^ ((ULL)rand() << 45) ^ ((ULL)rand() << 60);
}
// 初始化Zobrist表
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
// 设置棋盘尺寸和边界
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
// 落子
void Board::ChessDown(Pos next)
{
	int row = next.row;
	int col = next.col;

	level++;
	chess_map[row][col].color = player;
	zobristKey ^= zobristBoard[player][row][col];
	// 交换下棋方
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
// 取消落子
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
// 更新棋形
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
// 获取键值
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
// 判断key棋型，填充棋型表
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

	// 从左往右判断，然后从右往左判断
	int p1 = ShortLine(line_left);
	int p2 = ShortLine(line_right);

	// 如果两个方向都是眠三，有可能是活三，复查
	if (p1 == SLEEPTHREE && p2 == SLEEPTHREE)
	{
		return CheckThreeType(line_left);
	}
	// 如果两个方向都是眠四，有可能是活四，复查
	else if (p1 == RUSHFOUR && p2 == RUSHFOUR)
	{
		return CheckFourType(line_left);
	}
	// 返回二者中最大那个
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
	// 如果有两个空位置能成五，就是活四
	return five >= 2 ? LIVEFOUR : RUSHFOUR;
}
// 判断棋型
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
	// 计算中间空格
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
// 获取价值
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
// 初始化棋型数据
void Board::InitChessType()
{
	// 初始化棋型辅助表
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
	//初始化棋型表
	for (int key = 0; key < 65536; key++)
	{
		patternTable[key][0] = LineType(0, key);
		patternTable[key][1] = LineType(1, key);
	}
	//初始化走法评价表
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
	// 局面评价分值
	int value[8] = { 0, 2, 12, 18, 96, 144, 800, 1200 };

public:
	int sumPosition = 0;			// 搜索的棋形局面数
	int hashVisitCount = 0;			// hash表访问次数
	int searchDepth = 0;			// 实际搜索深度
	int timeLeft = 90000;		    // 一局棋的剩余思考时间
	int eachThinkTime = 1200;		// 每一步的思考时间
	int allThinkTime = 90000;	    // 一局棋总思考时间
	int ThinkTime = 0;				// 当前步的思考时间
	Point bestPoint;				// AI思考的最佳点
	MoveLine bestLine;			    // AI思考的最佳路线
	clock_t start, finish;			// AI开始和结束思考的时间点
	bool stopThink = false;			// AI是否停止思考

	// 搜索最佳点
	Pos SearchBest();
	// 返回最佳点
	Pos BestMove();
	// 插入排序
	void SortInsert(Point* a, int n);
	// 落子
	void SetChess(Pos next);
	// 写入哈希表
	void UpdateHash(int depth, int value, int hashtype);
	// 记录pv走法
	void RecordPVMove(Pos best);
	// 获取下一步走法
	Pos NextMove(MoveList& moveList);
	// 查询哈希表
	int SearchHash(int depth, int alpha, int beta);
	// 返回当前已用的搜索时间
	int GetUsedTime();
	// 返回每步可用的搜索时间
	int EachSearchTime();
	// 评价走法
	int EvaluateMove(OnePoint* c);
	// 搜索根节点
	Point RootSearch(int depth, int alpha, int beta, MoveLine* pline);
	// 核心：Alpha-Beta剪枝
	int AlphaBeta(int depth, int alpha, int beta, MoveLine* pline);
	// 裁剪走法列表，成功返回裁剪后的数量，无法裁剪返回0
	int CutMoveList(Pos* move, Point* tempMemList, int Csize);
	// 生成可行走法
	int GenerateMove(Pos* move);
	// 评价当前局面
	int Evaluate();

};
// 返回当前已用的搜索时间
int AI::GetUsedTime()
{
	return (double)(clock() - start) / CLOCKS_PER_SEC * 1000;
}
// 返回每步可用的搜索时间
int AI::EachSearchTime()
{
	return (eachThinkTime < timeLeft / 6) ? eachThinkTime : timeLeft / 6;
}
// 查询哈希表
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
// 写入哈希表
void AI::UpdateHash(int depth, int value, int hashtype)
{
	Hash* p_hash = &hashTable[zobristKey & (HASHSIZE - 1)];
	p_hash->key = zobristKey;
	p_hash->value = value;
	p_hash->hashtype = hashtype;
	p_hash->depth = depth;
}
// 界面落子
void AI::SetChess(Pos next)
{
	next.row += 4, next.col += 4;
	ChessDown(next);
}
// 返回最佳点
Pos AI::BestMove()
{
	Pos best = SearchBest();
	best.row -= 4, best.col -= 4;
	return best;
}
// 搜索最佳点
Pos AI::SearchBest()
{
	start = clock();
	sumPosition = 0;
	hashVisitCount = 0;

	Pos bestMove;
	// 第一步下中心点
	if (chessCount == 0)
	{
		bestMove.row = size / 2 + 4;
		bestMove.col = size / 2 + 4;
		return bestMove;
	}
	// 第二步随机选择第一手棋周围一格内的点, 第三步随机选择第一手棋周围两格内的点
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
	// 迭代加深搜索
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
// 搜索根节点
Point AI::RootSearch(int depth, int alpha, int beta, MoveLine* pline)
{
	Point best = rootMove[0];
	MoveLine line;

	if (depth == MINDEPTH)
	{
		Pos moves[64];
		rootMoveCount = GenerateMove(moves);
		// 只存在一个可行着法，直接返回
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

	// 遍历可选点
	int value;
	for (int i = 0; i < rootMoveCount; i++)
	{
		// 搜索非必败点
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
				// 保存路线
				pline->moves[0] = pos;
				memcpy(pline->moves + 1, line.moves, line.n * sizeof(Pos));
				pline->n = line.n + 1;
				// 找到必胜点直接返回
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
// 获取下一步走法
Pos AI::NextMove(MoveList& moveList)
{
	/*sign0:哈希表走法
	 *sign1:生成全部走法
	 *sign2:依次返回sign1中的走法
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
// 记录pv走法
void AI::RecordPVMove(Pos best)
{
	PrincipalVariatio* e = &pvsTable[zobristKey % PVSSIZE];
	e->key = zobristKey;
	e->best = best;
}
// Alpha-Beta剪枝算法
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
	//对方已成五
	if (CheckWin())
	{
		return -10000;
	}
	// 叶节点
	if (depth <= 0)
	{
		return Evaluate();
	}

	// 查询哈希表
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
		// 清空之前节点路线
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
// 棋型剪枝
int AI::CutMoveList(Pos* move, Point* tempMemList, int candCount)
{
	//存在活四或更厉害的棋形棋形，直接返回
	if (tempMemList[0].value >= 2400)
	{
		move[0] = tempMemList[0].pos;
		return 1;
	}
	int moveCount = 0;
	//对方活三
	if (tempMemList[0].value == 1200)
	{
		//寻找对方能活四的点
		for (int i = 0; i < candCount; i++)
		{
			if (tempMemList[i].value == 1200)
			{
				move[moveCount] = tempMemList[i].pos;
				moveCount++;
			}
			else break;
		}
		//寻找双方能冲四的点
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
// 生成走法
int AI::GenerateMove(Pos* move)
{
	int candCount = 0;                //待选走法数
	int moveCount = 0;                //筛选排序后的走法数
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
	// 按价值排序
	SortInsert(tempMemList, candCount);
	moveCount = CutMoveList(move, tempMemList, candCount);
	// 如果没有剪枝，复制前MaxMoves个走法
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
// 插入排序
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
// 局面估值
int AI::Evaluate()
{
	int playerType[8] = { 0 };               // 记录下子方棋形数
	int enemyType[8] = { 0 };                // 记录另一方棋形数
	int rushfour_temp = 0;			  	     // 缓存上次循环我方的冲四数量，用于判断活四，连续冲四

	// 统计两格以内的空位双方可以形成的棋形
	for (int i = board_start; i < board_end; ++i)
	{
		for (int j = board_start; j < board_end; ++j)
		{
			if (chess_map[i][j].numInTwoBlocks && chess_map[i][j].color == Empty)
			{
				rushfour_temp = playerType[RUSHFOUR];
				TypeCount(&chess_map[i][j], player, playerType);
				TypeCount(&chess_map[i][j], enemy, enemyType);
				//同一个点有两个冲四，那就相当于活四
				if (playerType[RUSHFOUR] - rushfour_temp >= 2)
				{
					playerType[RUSHFOUR] -= 2;
					playerType[LIVEFOUR]++;
				}
			}
		}
	}

	// 当前局面轮到己方下棋
	// 1.己方存在成五点
	// 2.对方存在两个成五点，必败
	// 3.对方不能成五，己方存在活四
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
// 走法打分
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