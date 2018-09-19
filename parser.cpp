
#include <cstdio>
#include <stdlib.h>
#include <stdio.h>
#include <iostream>
#include <fstream>
#include <stack>
#include <queue>
#include <string>
#include <cstring>
#include <vector>
#include <map>
#include <sstream>
#define ACT 30
#define ACC 1
#define GT 10

using namespace std;
ofstream asmCode("asmCode.txt");
ofstream opout("optmz.txt");
ofstream optBlock("optBlock.txt");
ofstream optMid("optMid.txt");
ofstream fout("output.txt");
ofstream mout("mid.txt");
ofstream tout("table.txt");
ifstream fin("data.txt");
//数据结构定义
struct produce
{
	string pre;
	string flw;
	int pos;
	int flwlen;
};

struct closure
{
	int k;
	std::vector<produce *> p;
};

struct quar {
	string a = "(\t";
	string q1;
	string b = ",\t";
	string q2;
	string c = ",\t";
	string q3;
	string d = ",\t";
	string q4;
	string e = ")\t";
};
int mid_sqz = 0;
quar* mid[300];
//符号的定义
struct sym {
	int sqz;
	string name;
	int type;
	int value;
};
//符号表的定义
struct symTable {
	int total;
	sym* sym_t[30];
};

symTable* smt = new(symTable);

//string prgm = "ni(ni){p(i);f(t){f;e}l{t;e}w(i<i){f(t){f;e}l{t;e}e}i=(i+m)*m;o(i;i<m;i=i+m){i=i+m;e}i>i;(!t&f);e}e#";
string prgm = "ni(ni){ni;i=m;ni;i=m;ni;i=m;o(i;i<m;i=i+m){f(i<m){i=i+m;e}l{i=i+m;e}e}p(i);p(i);ni;i=m;w(i>m){p(i);i=i-m;e}w(t){i=m;e}e}e#";
int val[300] = { 1,0,0,1,1,0,0,1,2,0,2,0,1,0,1,3,0,3,0,0,0,1,4,0,4,0,0,0,0,0,2,0,2,0,9,0,2,0,2,0,1,0,0,0,0,2,0,5,0,0,3,0,3,0,2,0,0,0,0,0,4,0,4,0,2,0,0,0,0,0,0,0,3,0,0,0,0,4,0,0,1,5,0,5,0,9,0,0,0,5,0,1,0,0,0,0,5,0,0,5,0,5,0,1,0,0,0,0,0,1,0,0,3,0,4,0,0,0,0,0,0,0 };
string s[] = {
	"P->FP#",//0
	"P->e",//1
	"F->R(R){B}",//2
	"B->SB",//3 
	"B->e",//4
	"S->R;",//声明语句5
	"S->C;",//运算语句6
	"S->G;",//逻辑运算语句7
	"S->K",//For循环8
	"S->L",//if   9
	"S->W",//while 10
	"S->M;",//print11
			//"S->N;"//scanf
			"R->Ti",//12
			"T->n",//13
				   //*****运算**********
				   "C->i=E",//14
				   "E->E+A",//15
				   "E->E-A",//16
				   "E->A",//17
				   "A->A*D",//18
				   "A->A/D",//19
				   "A->D",//20
				   "D->i",//21
				   "D->m",//22
				   "D->(E)",//23
							//***逻辑********
							"G->H|G",//24
							"G->H",//25
							"H->H&I",//26
							"H->I",//27
							"I->!I",//28
							"I->(G)",//29
							"I->t",//30
							"I->f",//31
							"I->J>J",//32
							"I->J<J",//33
							"I->J:J",//34
							"J->i",//35
							"J->m",//36
								   //***For循环****
								   "K->o(i;G;C){B}",//37
													//***if********
													"L->f(G){B}l{B}",//38
																	 //****while****
																	 "W->w(G){B}",//39
																				  //*****printf**
																				  "M->p(D)",//40
																							//****scanf****
																							//"N->s(i)"


};

string V[] = { "P","F","B","S","R","T","C","A","D","E","G","H","I","J","K","L","W","M" };
string T[] = { "e","i","n","(",")","{","}",";","+","-","*","/","=","m","#","|","&","!","t","f",">","<",":","o","f","l" ,"w","p" };
string Vstr = "P F B S R T C A D E G H I J K L W M ";
string Tstr = "e i n ( ) { } ; + - * / = m # | & ! t f > < : o f l w p ";

//存储SLR分析表
string action_v[300][300];
//int action_a[50][300];
int goto_t[300][300];

std::map<string, string> follow;  //存储follow集的映射
std::map<string, string> first;  //存储follow集的映射
std::map<string, int> through_ctrl;
std::map<string, int> fin_ctrl;
std::vector<produce *> prd; //存储产生式的vector
std::vector<closure*> clsr; //存储项目集规范族
std::map<string, int> midSqz;

//控制制表过程的字码
int ctrl_c;
int ctrl_p;
int prgmPos;
int equalPos;

//SLR分析需要的两个栈
stack<char> smb_stk;
stack<int> st_stk;
stack<int> if_flag;
stack<int> while_flag;
stack<int> for_flag;
stack<char> fow_state;
stack<int> fow_flag;


//功能函数定义
void make_follow(int n);
void make_closure();
void make_action(string s, int k);
void make_goto(string s, int k);
void make_reduce(produce* p);
void make_produce(string s);
void find_produce(produce* p, int type);
void initial();
void initial_thr_ctr(int Vlen);
string make_str(char a);
void prt_p(produce* p);
produce* add_pos(produce* p);
void initial_find_ctrl();
void prt_c(closure* c);
void prt_prd(std::vector<produce *> p);
int SLR(string prgm);
int do_goto();
void prt_int_stack(stack<int> s);
void prt_char_stack(stack<char> s);
void anly_cmp(int prd_sqz);
void anly_bool(int prd_sqz);
void anly_if(int prd_sqz);
void anly_for(int prd_sqz);
void anly_while(int prd_sqz);
void build_sym_table();
string queryTable(int a, int v, int t);
void build_sym_table();

void build_sym_table() {
	int i = 0;
	string s;
	while (getline(fin, s))
	{
		
		if (s.length() != 0)
		{
			smt->total = i+1;
			sym* sm = new(sym);
			sm->sqz = i;
			sm->name = s;
			sm->type = 0;
			sm->value = 0;
			smt->sym_t[i] = sm;
		}
		i++;
	}
}

string queryTable(int a, int v, int t) {
	switch (t)
	{
	case 1: {//声明语句
		if (smt->sym_t[a]->type == 0) {
			cout << "该变量尚未被定义" << endl;
			smt->sym_t[a]->type = v;
			return "error1";
		}cout << "该变量已经被定义，重复定义！" << endl;
		break;
	}
	case 2: {//查询符号名
		if (smt->sym_t[a]->type == 0) {
			cout << "该变量尚未被定义" << endl;
			return "error2";
		}
		else {
			return smt->sym_t[a]->name;
		}
		break;
	}
	
	default:
		break;
	}
	return "error3";
}

//语义函数定义



void anly_if(int prd_sqz) {
	fow_flag.pop();
	fow_state.pop();
}

void anly_while(int prd_sqz) {
	mid[while_flag.top()]->q4 = to_string(mid_sqz + 1);
	while_flag.pop();

	quar* q2 = new(quar);
	q2->q1 = "GOTO";
	q2->q4 = to_string(fow_flag.top());
	mid[mid_sqz] = q2;
	mid_sqz++;

	fow_flag.pop();
	fow_state.pop();
}



void anly_for(int prd_sqz) {
	mid[while_flag.top()]->q4 = to_string(mid_sqz + 1);
	while_flag.pop();

	quar* q2 = new(quar);
	q2->q1 = "GOTO";
	q2->q4 = to_string(fow_flag.top());
	mid[mid_sqz] = q2;
	mid_sqz++;

	fow_flag.pop();
	fow_state.pop();
}

void anly_print(int prd_sqz) {
	string pre = prd[prd_sqz]->pre;
	quar* q2 = new(quar);
	q2->q1 = "PRINT";
	q2->q2 = prd[prd_sqz]->flw[2] + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
	//mout << mid_sqz << ":" << q2->a << q2->q1 << q2->b << q2->q2 << q2->c << q2->q3 << q2->d << q2->q4 << q2->e << endl;
	mid[mid_sqz] = q2;
	mid_sqz++;
}

void anly_release(int prd_sqz) {

	quar* q2 = new(quar);
	q2->q1 = "RELEASE";
	//mout << mid_sqz << ":" << q2->a << q2->q1 << q2->b << q2->q2 << q2->c << q2->q3 << q2->d << q2->q4 << q2->e << endl;
	mid[mid_sqz] = q2;
	mid_sqz++;
}
int type;
void anly_pronounce(int prd_sqz) {
	if (prd_sqz == 13) {
		type = val[prgmPos];
	}
	else {
		queryTable(val[prgmPos], type, 1);
	}
}

/****************************构造产生式*******************************/
void make_produce(string s) {    //理解文法，构造产生式
	int len = s.length();
	produce* p = new(produce);
	int f = s.find("->", 0);
	p->pre = s.substr(0, f);
	p->flw = s.substr(f + 2, len - f - 2);
	p->pos = 0;
	p->flwlen = p->flw.length();

	prd.push_back(p);

}
/***************************计算FOLLOW集*****************************/
void prt_fst() {
	map<string, string>::const_iterator it;
	for (it = first.begin(); it != first.end(); it++)
		fout << it->first << " = " << it->second << endl;
}

void make_first() {
	int tNum = Tstr.length() / 2;
	for (int i = 0; i < tNum; i++) {
		//fout<<i;
		string t = Tstr.substr(i * 2, 1);
		first[t] = t;
	}
	prt_fst();
	int flag = 1;
	tNum = prd.size();
	while (flag != 0) {
		//prt_fst();
		flag = 0;
		for (int i = 0; i < tNum; i++) {
			string a = prd[i]->pre;
			string b = prd[i]->flw;
			int l = b.length();
			if (first.count(a) == 1) {
				for (int j = 0; j < 1; j++) {
					string c = b.substr(j, 1);
					//fout<<c<<endl;
					if (first.count(c) == 1) {
						string d = first[c];
						for (int k = 0; k < d.length(); k++) {
							string e = d.substr(k, 1);
							//fout<<e<<endl;
							if (first[a].find(e) == string::npos) {
								flag++;
								first[a] += (e + " ");
							}
						}
					}
					else {
						first[c] = " ";
						flag++;
					}
				}
			}
			else {
				first[a] = " ";
				flag++;
			}
		}
	}
	prt_fst();
}


void make_follow(int n) {

	for (int i = 0; i < n; i++)
		follow[V[i]] = " ";
	//follow["P"] = "  #";

	for (int i = 0; i < prd.size(); i++) {
		string s = prd[i]->flw;
		for (int i = 1; i < s.length(); i++) {
			if (Tstr.find(s[i]) != string::npos && Vstr.find(s[i - 1]) != string::npos && follow[s.substr(i - 1, 1)].find(s[i]) == string::npos) {
				string s1 = " " + s.substr(i, 1);
				follow[s.substr(i - 1, 1)] += s1;
			}
		}
	}

	for (int i = 0; i < n; i++) {
		//fout<<"follow1 "<<V[i]<<" :"<<follow[V[i]]<<endl;
	}

	for (int i = 0; i < prd.size(); i++) {
		string pre = prd[i]->pre;
		string flw = prd[i]->flw;
		int len = prd[i]->flwlen;
		for (int j = 0; j < len - 1; j++) {
			string a = flw.substr(j, 1);
			string b = flw.substr(j + 1, 1);
			if (Vstr.find(a) != string::npos && Vstr.find(b) != string::npos) {
				string c = first[b];
				int l = c.length();
				for (int k = 0; k < l; k++) {
					string d = c.substr(k, 1);
					if (follow[a].find(d) == string::npos) {
						follow[a] += (d + " ");
					}
				}
			}
		}
	}


	for (int i = 0; i < prd.size(); i++) {
		string pre = prd[i]->pre;
		string flw = prd[i]->flw;
		int len = prd[i]->flwlen;
		if (Vstr.find(flw[len - 1]) != string::npos) {
			for (int i = 0; i < follow[pre].length(); i++) {
				if (follow[flw.substr(len - 1, 1)].find(follow[pre].substr(i, 1)) == string::npos) {
					follow[flw.substr(len - 1, 1)] += " " + follow[pre].substr(i, 1);
				}
			}
		}
	}



	for (int i = 0; i < n; i++) {
		fout << "follow(" << V[i] << "):" << follow[V[i]] << endl;
	}
}

/*****************************建立SLR分析表所用的函数*******************************/

void make_action(string s, int k) {
	int i = ctrl_c;
	int j = Tstr.find(s) / 2;
	if (s == "#") {
		action_v[i][j] = "A";
	}
	else {
		string a = "S";
		char b[3];
		sprintf(b, "%d", k);
		a = a + b;
		action_v[i][j] = a;
	}
}

void make_goto(string s, int k) {
	int i = ctrl_c;
	int j = Vstr.find(s) / 2;
	goto_t[i][j] = k;
}

void make_reduce(produce* p) {
	//fout<<"减了减了"<<endl;
	for (int i = 0; i < prd.size(); i++) {
		if (p->pre == prd[i]->pre && p->flw == prd[i]->flw) {
			string a = "R";
			char b[3];
			sprintf(b, "%d", i);
			a = a + b;
			string s = p->pre;
			string str = follow[s];
			//fout<<str<<"a = "<<a<<endl;
			for (int j = 0; j < str.length(); j++) {
				if (Tstr.find(str[j]) != string::npos && str[j] != ' ') {
					//fout<<"真的填了 填在了ctrl_c: "<<ctrl_c<<"Tstr.find(str[i]).2: "<<Tstr.find(str[j])/2<<endl;

					action_v[ctrl_c][Tstr.find(str[j]) / 2] = a;
				}
			}
		}
	}
}

void find_produce(produce* p, int type, string s) { //观察某个项目是否已经出现在集合之中，type 1：V 2：T
	int n = clsr.size();
	int flag = 0;
	//prt_p(p);

	for (int i = 0; i < n; i++) {
		int l = clsr[i]->p.size();
		for (int j = 0; j < l; j++) {
			//prt_p(p);
			//prt_p(clsr[i]->p[j]);
			produce* np = clsr[i]->p[j];
			if (p->pre == np->pre && p->flw == np->flw && p->pos == np->pos) {
				flag = 1;
				//fout<<"找到了！"<<endl;
				if (type == 1) {
					if (fin_ctrl[s] == 0) {
						make_goto(s, i);
					}
					else {
						clsr[fin_ctrl[s]]->p.push_back(p);
					}
				}
				else {
					make_action(s, i);
				}
			}
		}
	}

	if (flag == 0) {
		if (fin_ctrl[s] == 0) {
			closure* c = new(closure);
			c->k = clsr.size();
			c->p.push_back(p);
			clsr.push_back(c);
			fin_ctrl[s] = c->k;
			//fout<<"创建了闭包"<<c->k<<endl;
			make_goto(s, c->k);
		}
		else {
			closure* c = new(closure);
			c->k = fin_ctrl[s];
			c->p.push_back(p);
			clsr[fin_ctrl[s]]->p.push_back(p);
			//fout<<"加入了闭包"<<c->k<<endl;
		}

		if (type == 1) {
			make_goto(s, fin_ctrl[s]);
		}
		else {
			make_action(s, fin_ctrl[s]);
		}
	}

}

void through_prd(string s, int k) {
	for (int i = 0; i < prd.size(); i++) {
		if (s == prd[i]->pre) {
			clsr[ctrl_c]->p.push_back(prd[i]);
		}
	}
	through_ctrl[s] = 1;
}

//创建项目集规范族,并同步形成SLR（1）分析表
void make_closure() {
	while (ctrl_c < clsr.size()) {
		//fout<<"当前处于第"<<ctrl_c<<"个闭包"<<endl;
		//prt_c(clsr[ctrl_c]);
		initial_thr_ctr(sizeof(V) / sizeof(V[0]));
		initial_find_ctrl();
		ctrl_p = 0;
		while (ctrl_p < clsr[ctrl_c]->p.size()) {

			//fout<<"队列长度："<<clsr[ctrl_c]->p.size()<<endl;

			string pre = clsr[ctrl_c]->p[ctrl_p]->pre;
			string flw = clsr[ctrl_c]->p[ctrl_p]->flw;
			int pos = clsr[ctrl_c]->p[ctrl_p]->pos;
			int flwlen = clsr[ctrl_c]->p[ctrl_p]->flwlen;
			//fout<<"已经遍历到"<<pre<<"->"<<flw<<endl;


			if (pos < flwlen) {
				string s = flw.substr(pos, 1);

				if (Vstr.find(s) != string::npos) {

					if (through_ctrl[s] == 0) {
						//fout<<"s = "<<s<<endl;
						//fout<<"对符号"<<s<<"进行补充"<<endl;
						through_prd(s, 1);
						//prt_c(clsr[ctrl_c]);
					}
					find_produce(add_pos(clsr[ctrl_c]->p[ctrl_p]), 1, s);
				}
				else {
					if (Tstr.find(s) != string::npos) {
						find_produce(add_pos(clsr[ctrl_c]->p[ctrl_p]), 2, s);
					}
				}
				ctrl_p++;
			}
			else {

				make_reduce(clsr[ctrl_c]->p[ctrl_p]);
				ctrl_p++;
			}

		}

		ctrl_c++;
		//initial_thr_ctr(sizeof(V)/sizeof(V[0]));
		//fout<<"ctrl_c = "<<ctrl_c<<" clsr.size() = "<<clsr.size()<<endl;

	}
}

void initial() {
	ctrl_p = 0;
	ctrl_c = 0;
	closure* c = new(closure);
	c->k = 0;
	c->p.push_back(prd[0]);
	clsr.push_back(c);
	midSqz["A"] = 0;
	midSqz["D"] = 0;
	midSqz["E"] = 0;
	midSqz["G"] = 0;
	midSqz["H"] = 0;
	midSqz["I"] = 0;
	midSqz["J"] = 0;
	//fout<<"clsr.size 1 = "<<clsr.size()<<endl;
	//memset(action_a,1,50*300);
	//memset(action_v,1,50*300);
	//memset(goto_t,1,20*300);
}

void initial_thr_ctr(int Vlen) {
	for (int i = 0; i < Vlen; i++)
		through_ctrl[V[i]] = 0;
	//fout<<through_ctrl.size()<<endl;
}

void initial_find_ctrl() {
	for (int i = 0; i < sizeof(V) / sizeof(V[0]); i++)
		fin_ctrl[V[i]] = 0;
	for (int i = 0; i < sizeof(T) / sizeof(T[0]); i++)
		fin_ctrl[T[i]] = 0;

}

/***************************SLR分析函数******************************/
void ini_stk() {
	st_stk.push(0);
}

int do_rdc(string s) {

	int len = s.length();
	string num = s.substr(1, len - 1);
	int state;
	state = atoi(num.c_str());
	//if (state > 4 && state < 12)
		//anly_release(state);
	if (state > 11 && state < 14)
		anly_pronounce(state);
	if (state > 13 && state < 24)
		anly_cmp(state);
	if (state > 23 && state < 37)
		anly_bool(state);
	if (state == 37)
		anly_for(state);
	if (state == 38)
		anly_if(state);
	if (state == 39)
		anly_while(state);
	if (state == 40)
		anly_print(state);

	char pre = prd[state]->pre[0];
	int time = prd[state]->flwlen;
	fout << "规约，规约规则为：" << prd[state]->pre << "->" << prd[state]->flw << endl;
	for (int i = 0; i < time; i++) {
		st_stk.pop();
		smb_stk.pop();
	}

	smb_stk.push(pre);
	prt_int_stack(st_stk);
	fout << endl;
	prt_char_stack(smb_stk);
	fout << endl;
	do_goto();

	return 0;
}

int do_goto() {


	int i = st_stk.top();
	char c = smb_stk.top();
	int j = Vstr.find(c) / 2;
	fout << "跳转，转向的状态为： " << goto_t[i][j] << endl;
	st_stk.push(goto_t[i][j]);


	prt_int_stack(st_stk);
	fout << endl;
	prt_char_stack(smb_stk);
	fout << endl;
	return 0;
}

int do_shft(string s, char c) {
	//fout<<"移入,移入后栈的情况："<<endl;
	smb_stk.push(c);
	int len = s.length();
	string num = s.substr(1, len - 1);
	int state;
	state = atoi(num.c_str());
	st_stk.push(state);

	prt_int_stack(st_stk);
	fout << endl;
	prt_char_stack(smb_stk);
	fout << endl;
	return 0;
}

int SLR(string prgm) {
	int len = prgm.length();
	int i = 0;
	int flag = 0;
	while (i < len && flag == 0) {
		prgmPos = i - 1;
		char ahead = prgm[i];
		char next = prgm[i + 1];
		int pos = Tstr.find(ahead) / 2;
		int state = st_stk.top();
		string act = action_v[state][pos];
		char a = act[0];
		fout << "读入的字符为：" << ahead << " 要做的动作为： " << act << endl;
		switch (a) {
		case 'S':
			if (ahead == '=') {//记录赋值语句的等号位置
				equalPos = i - 1;
			}
			if (ahead == 'f' && next == '(') {
				fow_state.push('f');
				fow_flag.push(0);
			}
			if (ahead == 'w') {
				fow_state.push('w');
				fow_flag.push(mid_sqz);
			}
			if (ahead == 'o') {
				fow_state.push('o');
				fow_flag.push(mid_sqz);
			}
			if (!fow_state.empty()) {
				//mout << ahead << fow_state.top() << fow_flag.top() << endl;
				if (ahead == '{' && fow_state.top() == 'f' && fow_flag.top() == 0) {
					
					if_flag.push(mid_sqz);
					fow_flag.top()++;
					quar* q2 = new(quar);
					q2->q1 = "JE";
					q2->q2 = "G" + to_string(midSqz["G"] - 1);
					q2->q3 = "0";
					//mout << mid_sqz << ":" << q2->a << q2->q1 << q2->b << q2->q2 << q2->c << q2->q3 << q2->d << q2->q4 << q2->e << endl;
					mid[mid_sqz] = q2;
					mid_sqz++;
				}
				if (ahead == 'l' && fow_state.top() == 'f' && fow_flag.top() == 1) {
					mid[if_flag.top()]->q4 = to_string(mid_sqz + 1);
					if_flag.pop();
					if_flag.push(mid_sqz);
					fow_flag.top()++;
					quar* q2 = new(quar);
					q2->q1 = "GOTO";
					//mout << mid_sqz << ":" << q2->a << q2->q1 << q2->b << q2->q2 << q2->c << q2->q3 << q2->d << q2->q4 << q2->e << endl;
					mid[mid_sqz] = q2;
					mid_sqz++;
				}
				if (ahead == '}' && fow_state.top() == 'f' && fow_flag.top() == 2) {
					mid[if_flag.top()]->q4 = to_string(mid_sqz);
					if_flag.pop();
				}
				if (fow_state.top() == 'w' && ahead == '{') {
					while_flag.push(mid_sqz);

					quar* q2 = new(quar);
					q2->q1 = "JE";
					q2->q2 = "G" + to_string(midSqz["G"] - 1);
					q2->q3 = "0";
					mid[mid_sqz] = q2;
					mid_sqz++;
				}
				if (fow_state.top() == 'o' && ahead == '{') {
					while_flag.push(mid_sqz);

					quar* q2 = new(quar);
					q2->q1 = "JE";
					q2->q2 = "G" + to_string(midSqz["G"] - 1);
					q2->q3 = "0";
					mid[mid_sqz] = q2;
					mid_sqz++;
				}

			}





			do_shft(act, ahead);
			i++;
			break;
		case 'R':
			do_rdc(act);
			break;
		case 'A':
			fout << "输入程序符合语法规则，识别成功" << endl;
			i++;
			break;
		default:
			fout << "输入程序不符合语法规则，识别失败" << endl;
			flag = 1;
			break;
		}
	}

	return 0;
}

/************************************调试与辅助函数********************/
void prt_p(produce *p) {
	fout << p->pre << "->" << p->flw << " pos: " << p->pos << " flwlen: " << p->flwlen << endl;
}

void prt_c(closure * c) {
	fout << "闭包" << c->k << endl;
	prt_prd(c->p);
}

void prt_prd(std::vector<produce *> p) {
	for (int i = 0; i < p.size(); i++) {
		fout << p[i]->pre << "->" << p[i]->flw << " " << "pos: " << p[i]->pos << " flwlen: " << p[i]->flwlen << endl << endl;
	}
}

void prt_clsr() {
	for (int i = 0; i < clsr.size(); i++) {
		fout << "闭包" << clsr[i]->k << endl;
		prt_prd(clsr[i]->p);
	}
}

void prt_int_stack(stack<int> s) {

	int len = s.size();
	stack<int> a;
	int tmp;

	for (int i = 0; i < len; i++) {
		tmp = s.top();
		s.pop();
		a.push(tmp);
	}

	for (int i = 0; i < len; i++) {
		tmp = a.top();
		fout << tmp << " ";
		a.pop();
		s.push(tmp);
	}
}

void prt_char_stack(stack<char> s) {

	int len = s.size();
	stack<char> a;
	char tmp;

	for (int i = 0; i < len; i++) {
		tmp = s.top();
		s.pop();
		a.push(tmp);
	}

	for (int i = 0; i < len; i++) {
		tmp = a.top();
		fout << tmp << " ";
		a.pop();
		s.push(tmp);
	}
}

produce* add_pos(produce* p) {
	produce* np = new(produce);
	*np = *p;
	np->pos++;
	return np;
}

void prt_action() {
	int a = sizeof(T) / sizeof(T[0]);
	int b = clsr.size();
	int c = sizeof(V) / sizeof(V[0]);
	printf("\t");
	for (int i = 0; i < a; i++)
		fout << T[i] << "\t";
	printf("|\t");
	for (int i = 1; i < c; i++)
		fout << V[i] << "\t";
	printf("\n");
	for (int i = 0; i < b; i++) {
		printf("%d\t", i);
		for (int j = 0; j < a; j++) {
			fout << action_v[i][j] << "\t";
		}
		printf("|\t");
		for (int j = 1; j < c; j++) {
			if (goto_t[i][j] != 0)
				fout << goto_t[i][j] << "\t";
			else
				fout << "\t";
		}
		printf("\n");
	}

}
/**********************语义函数*****************************************/
void anly_cmp(int prd_sqz) {
	string pre = prd[prd_sqz]->pre;
	quar* q = new(quar);

	switch (prd[prd_sqz]->flwlen)
	{
	case 1: {
		if (prd[prd_sqz]->flw == "i") {
			q->q1 = "=";
			q->q2 = queryTable(val[prgmPos],1,2) + ".addr";
			q->q4 = pre + to_string(midSqz[pre]);
		}
		else {
			if (prd[prd_sqz]->flw == "m") {
				q->q1 = "=";
				q->q2 = to_string(val[prgmPos]);
				q->q4 = pre + to_string(midSqz[pre]);
			}
			else {
				q->q1 = "=";
				q->q2 = prd[prd_sqz]->flw + to_string(midSqz[prd[prd_sqz]->flw] - 1);
				q->q4 = pre + to_string(midSqz[pre]);
			}
		}
		break;
	}
	case 3: {
		if (prd_sqz == 14) {//C->i=E
			q->q1 = prd[prd_sqz]->flw[1];
			q->q4 = queryTable(val[equalPos], 1, 2) + ".addr";
			q->q2 = prd[prd_sqz]->flw[2] + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
		}
		else {
			if (prd_sqz == 23) {
				q->q1 = "=";
				q->q2 = prd[prd_sqz]->flw.substr(1, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(1, 1)] - 1);
				q->q4 = pre + to_string(midSqz[pre]);
			}
			else {
				q->q1 = prd[prd_sqz]->flw.substr(1, 1);
				q->q2 = prd[prd_sqz]->flw.substr(0, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(0, 1)] - 1);
				q->q3 = prd[prd_sqz]->flw.substr(2, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
				q->q4 = pre + to_string(midSqz[pre]);
			}
		}

		break;
	}

	default:
		break;
	}
	//mout << mid_sqz << ":" << q->a << q->q1 << q->b << q->q2 << q->c << q->q3 << q->d << q->q4 << q->e << endl;
	mid[mid_sqz] = q;
	mid_sqz++;
	midSqz[pre] ++;
}

void anly_bool(int prd_sqz) {
	string pre = prd[prd_sqz]->pre;
	quar* q = new(quar);
	if (prd_sqz == 30) {//"I->t"
		q->q1 = "=";  q->q2 = to_string(1);  q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 31) {//"I->f"
		q->q1 = "=";  q->q2 = to_string(0);  q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 35) {//"J->i"
		q->q1 = "=";  q->q2 = queryTable(val[prgmPos], 1, 2) + ".addr";  q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 36) {//"J->m"
		q->q1 = "=";  q->q2 = to_string(val[prgmPos]);  q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 25 || prd_sqz == 27) {//"G->H",//25 "H->I",//27
		q->q1 = "=";
		q->q2 = prd[prd_sqz]->flw + to_string(midSqz[prd[prd_sqz]->flw] - 1);
		q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 24) {//"G->H|G",//24
		q->q1 = "OR";
		q->q2 = prd[prd_sqz]->flw.substr(0, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(0, 1)] - 1);
		q->q3 = prd[prd_sqz]->flw.substr(2, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
		q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 26) {//"H->H&I",//26
		q->q1 = "AND";
		q->q2 = prd[prd_sqz]->flw.substr(0, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(0, 1)] - 1);
		q->q3 = prd[prd_sqz]->flw.substr(2, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
		q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 28) {//"I->!I",//28
		q->q1 = "NOT";
		q->q2 = prd[prd_sqz]->flw.substr(1, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(1, 1)] - 1);
		q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 29) {//"I->(G)",//29
		q->q1 = "=";
		q->q2 = prd[prd_sqz]->flw.substr(1, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(1, 1)] - 1);
		q->q4 = pre + to_string(midSqz[pre]);
	}
	if (prd_sqz == 32 || prd_sqz == 33 || prd_sqz == 34) {//"I->J>J",//32 "I->J<J",//33 "I->J:J",//34
		quar* q1 = new(quar);

		if (prd_sqz == 32 || prd_sqz == 33) {
			q1->q1 = "JB";
			if (prd_sqz == 32) {
				q1->q2 = prd[prd_sqz]->flw.substr(2, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
				q1->q3 = prd[prd_sqz]->flw.substr(0, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(0, 1)] - 2);
			}
			else {
				q1->q2 = prd[prd_sqz]->flw.substr(0, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(0, 1)] - 2);
				q1->q3 = prd[prd_sqz]->flw.substr(2, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
			}
		}
		else {
			q1->q1 = "JE";
			q1->q2 = prd[prd_sqz]->flw.substr(0, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(0, 1)] - 1);
			q1->q3 = prd[prd_sqz]->flw.substr(2, 1) + to_string(midSqz[prd[prd_sqz]->flw.substr(2, 1)] - 1);
		}
		q1->q4 = to_string(mid_sqz + 3);
		//mout << mid_sqz << ":" << q1->a << q1->q1 << q1->b << q1->q2 << q1->c << q1->q3 << q1->d << q1->q4 << q1->e << endl;
		mid[mid_sqz] = q1;
		mid_sqz++;
		quar* q2 = new(quar);
		q2->q1 = "=";
		q2->q2 = to_string(0);
		q2->q4 = pre + to_string(midSqz[pre]);
		//mout << mid_sqz << ":" << q2->a << q2->q1 << q2->b << q2->q2 << q2->c << q2->q3 << q2->d << q2->q4 << q2->e << endl;
		mid[mid_sqz] = q2;
		mid_sqz++;
		quar* q3 = new(quar);
		q3->q1 = "GOTO";
		q3->q4 = to_string(mid_sqz + 2);
		//mout << mid_sqz << ":" << q3->a << q3->q1 << q3->b << q3->q2 << q3->c << q3->q3 << q3->d << q3->q4 << q3->e << endl;
		mid[mid_sqz] = q3;
		mid_sqz++;
		quar* q4 = new(quar);
		q4->q1 = "=";
		q4->q2 = to_string(1);
		q4->q4 = pre + to_string(midSqz[pre]);
		//mout << mid_sqz << ":" << q4->a << q4->q1 << q4->b << q4->q2 << q4->c << q4->q3 << q4->d << q4->q4 << q4->e << endl;
		mid[mid_sqz] = q4;
		mid_sqz++;

		midSqz[pre] ++;
		return;
	}

	//mout << mid_sqz << ":" << q->a << q->q1 << q->b << q->q2 << q->c << q->q3 << q->d << q->q4 << q->e << endl;
	mid[mid_sqz] = q;
	mid_sqz++;
	midSqz[pre] ++;
	return;
}
/************************************中间代码优化**************************************/
//优化栈
stack<quar*> optmz;
//queue<quar*> opout;

struct block
{
	int start;
	int end;
	int Next;
	int jumpNext;
};

int inOutFlag[300];
int blockNum;
block* blockArray[30];
void makeBlock() {
	inOutFlag[0] = 1;
	inOutFlag[mid_sqz] = 2;
	for (int i = 0; i < mid_sqz; i++) {
		if (mid[i]->q1 == "JB" || mid[i]->q1 == "JE" || mid[i]->q1 == "GOTO") {
			if (inOutFlag[i] == 1) {
				inOutFlag[i] = 3;
				inOutFlag[i + 1] = 1;
			}
			else {
				inOutFlag[i] = 2;
				inOutFlag[i + 1] = 1;
			}
			
			int next = atoi(mid[i]->q4.c_str());
			//cout << "i: " << i << " next: " << next << endl;
			inOutFlag[next] = 1;
			if (next != 0) {
				if (inOutFlag[next - 1] == 1) {
					inOutFlag[next - 1] = 3;
				}
				else {
					inOutFlag[next - 1] = 2;
				}
				
			}
		}
	}

	for (int i = 0; i < mid_sqz; i++) {
		if (inOutFlag[i] == 1) {
			block* b = new block();
			b->start = i;
			blockArray[blockNum] = b;
		}
		if (inOutFlag[i] == 2) {
			blockArray[blockNum]->end = i;
			blockArray[blockNum]->Next = blockNum + 1;
			blockNum++;
			//cout << "第" << blockNum << "个block已生成" << endl;
		}
		if (inOutFlag[i] == 3) {
			block* b = new block();
			b->start = i;
			b->end = i;
			b->Next = blockNum + 1;
			blockArray[blockNum] = b;
			blockNum++;
			//cout << "第" << blockNum << "个block已生成" << endl;
		}
	}
	for (int i = 0; i < blockNum; i++) {
		string q1 = mid[blockArray[i]->end]->q1;
		if (q1 == "JB" || q1 == "JE" || q1 == "GOTO") {
			
			for (int j = 0; j < blockNum; j++) {
				int q4 = atoi(mid[blockArray[i]->end]->q4.c_str());
				if (q4 <= blockArray[j]->end) {
					blockArray[i]->jumpNext = j;
					break;
				}
				if (q4 > blockNum) {
					blockArray[i]->jumpNext = blockNum;
				}
			}
		}
	}
}

int midType(quar * q) {
	return 0;
}

int opedMidSeq;
quar* opedMid[300];

void optmize() {
	opedMidSeq = 0;
	for (int i = 0; i < blockNum; i++) {
		int s = blockArray[i]->start;
		int e = blockArray[i]->end;
		int opedStart = opedMidSeq;
		int opedEnd;
		int flag = 0;
		if (s != e) {
			for (int j = s; j < e + 1; j++) {
				//opout << j << ":" << mid[j]->a << mid[j]->q1 << mid[j]->b << mid[j]->q2 << mid[j]->c << mid[j]->q3 << mid[j]->d << mid[j]->q4 << mid[j]->e << endl;
				if (mid[j]->q1 == "=" && mid[j+1]->q1 == "=" && mid[j]->q4 == mid[j + 1]->q2) {
					if (flag == 0) {
						quar* q = new quar();
						q->q1 = "=";
						q->q2 = mid[j]->q2;
						q->q4 = mid[j + 1]->q4;
						//opout << "opedMidSeq1: " << opedMidSeq << endl;
						opedMid[opedMidSeq] = q;
						flag = 1;
					}
					else {
						opedMid[opedMidSeq]->q4 = mid[j + 1]->q4;
					}
				}
				else {
					if (mid[j]->q1 == "=" && flag == 1) {
						//opout << "opedMidSeq2: " << opedMidSeq << endl;
						opedMidSeq++;
						flag = 0;
					}
					else {
						//opout << "opedMidSeq3: " << opedMidSeq << endl;
						opedMid[opedMidSeq] = mid[j];
						opedMidSeq++;
						flag = 0;
					}
				} 
			}
			opedEnd = opedMidSeq - 1;
		}
		else {
			//opout << s << ":" << mid[s]->a << mid[s]->q1 << mid[s]->b << mid[s]->q2 << mid[s]->c << mid[s]->q3 << mid[s]->d << mid[s]->q4 << mid[s]->e << endl;

			//opout << "opedMidSeq4: " << opedMidSeq << endl;
			opedMid[opedMidSeq] = mid[s];
			opedMidSeq++;
			opedEnd = opedMidSeq - 1;
		}
		blockArray[i]->start = opedStart;
		blockArray[i]->end = opedEnd;
	}
	for (int i = 0; i < blockNum; i++) {
		string q1 = opedMid[blockArray[i]->end]->q1;
		if (q1 == "JB" || q1 == "JE" || q1 == "GOTO") {
			if (blockArray[i]->jumpNext >= blockNum) {
				opedMid[blockArray[i]->end]->q4 = to_string(opedMidSeq);
			}
			else {
				opedMid[blockArray[i]->end]->q4 = to_string(blockArray[blockArray[i]->jumpNext]->start);
			}
		}
	}
}
/***********************************汇编代码生成******************************************/

std::map<string, string> regAl;
int regAlNun = 0;
string allocateReg(string v) {
	string reg[4] = { "EAX","EBX","ECX","EDX" };
	if (regAl.count(v) != 0) {
		return regAl[v];
	}
	else {
		regAl[v] = reg[regAlNun % 4];
		regAlNun++;
		return regAl[v];
	}
}

string modifyQuar(string s) {
	if (s.find('.') != string::npos) {
		return s.substr(0, s.find('.'));
	}
	else {
		int len = s.length();
		int flag = 0;
		for (int i = 0; i < len; i++) {
			if (s[i] >= '0' && s[i] <= '9') {
				
			}
			else {
				flag++;
			}
			if (flag == 0) {
				return s;
			}
			else {
				return allocateReg(s);
			}

		}
	}
}

void printQuar(quar* q,int jump) {
	string q1 = q->q1;
	string q2 = q->q2;
	string q3 = q->q3;
	string q4 = q->q4;
	if (q1 == "=") {
		asmCode << "MOV" << "\t" << modifyQuar(q4) << "\t" << modifyQuar(q2) << "\t" << endl;
		return;
	}
	if (q1 == "+") {
		asmCode << "ADD" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "MOV" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q4) << "\t" << endl;
		return;
	}
	if (q1 == "-") {
		asmCode << "SUB" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "MOV" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q4) << "\t" << endl;
		return;
	}
	if (q1 == "*") {
		asmCode << "MUL" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "MOV" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q4) << "\t" << endl;
		return;
	}
	if (q1 == "/") {
		asmCode << "DIV" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "MOV" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q4) << "\t" << endl;
		return;
	}
	if (q1 == "NOT") {
		asmCode << "NOT" << "\t" << modifyQuar(q2) <<  "\t" << endl;
		return;
	}
	if (q1 == "AND") {
		asmCode << "AND" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "MOV" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q4) << "\t" << endl;
		return;
	}
	if (q1 == "OR") {
		asmCode << "AND" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "MOV" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q4) << "\t" << endl;
		return;
	}
	if (q1 == "JB") {
		asmCode << "CMP" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "JB" << "\t" << "L" << jump<< "\t" << endl;
		return;
	}
	if (q1 == "JE") {
		asmCode << "CMP" << "\t" << modifyQuar(q2) << ",\t" << modifyQuar(q3) << "\t" << endl;
		asmCode << "\t" << "JE" << "\t" << "L" << jump << "\t" << endl;
		return;
	}
	if (q1 == "GOTO") {
		asmCode << "JMP" << "\t" <<"L" <<jump << "\t" << endl;
		return;
	}
	if (q1 == "PRINT") {
		asmCode << "MOV" << "\t" << "EAX" << ",\t" << modifyQuar(q2) << "\t" << endl;
		asmCode << "\t" << "CALL" << "\t" << "WriteInt" << "\t" << endl;
		asmCode << "\t" << "EXIT" << "\t" << "\t" << endl;
		return;
	}
}

void makeAsm() {
	asmCode << ".data" << endl;
	for (int i = 0; i < smt->total; i++) {
		asmCode << smt->sym_t[i]->name<<"\t" <<" WORD " << "\t" <<" 0 "<< endl;
	}
	asmCode << ".code" << endl;
	asmCode << "mian PROC" << endl;
	for (int i = 0; i < blockNum; i++) {
		int start = blockArray[i]->start;
		int end = blockArray[i]->end;
		int jump = blockArray[i]->jumpNext;
		for (int j = start; j <= end; j++) {
			if (j == start) {
				asmCode << "L" << i << ":\t";
			}
			else {
				asmCode << "\t";
			}
			quar* q = opedMid[j];
			printQuar(q, jump);

		}
		
	}
	asmCode << "L" << 20<< ":\t"<<"mian ENDP"<<endl;
	asmCode << "END main" << endl;

}

/******************************main函数******************************/
int main() {


	build_sym_table();

	for (int i = 0; i < 41; i++)
		make_produce(s[i]);

	fout << "------------------建立FOLLOW集---------------------------------------" << endl;
	make_first();
	make_follow((sizeof(V) / sizeof(V[0])));

	initial();

	initial_thr_ctr(sizeof(V) / sizeof(V[0]));

	//	fout<<"a"<<endl;
	fout << "------------------求项目集规范族，并在此过程中建立SLR分析表----------------" << endl;

	make_closure();
	//add_pos(prd[0]);
	//prt_prd(prd);
	prt_clsr();
	fout << "------------------求得的分析表为：-------------------------------------" << endl;
	prt_action();
	ini_stk();
	//fout<<st_stk.top()<<endl;
	fout << "------------------进行语法分析：---------------------------------------" << endl;
	SLR(prgm);
	for (int i = 0; i < mid_sqz; i++)
		mout << i << ":" << mid[i]->a << mid[i]->q1 << mid[i]->b << mid[i]->q2 << mid[i]->c << mid[i]->q3 << mid[i]->d << mid[i]->q4 << mid[i]->e << endl;
	tout << "sqz:" << "\t" << "name:" << "\t" << "type" << "\t" << "value" << "\t" << endl;
	for(int i = 0; i < smt->total; i ++)
		tout << smt->sym_t[i]->sqz << "\t" << smt->sym_t[i]->name << "\t" << smt->sym_t[i]->type << "\t" << smt->sym_t[i]->value << "\t" << endl;
	makeBlock();
	for (int i = 0; i < blockNum; i++) {
		opout << i << ":" << blockArray[i]->start << "  " << blockArray[i]->end << "  " << blockArray[i]->Next << "  " << blockArray[i]->jumpNext << "  " << endl;
	}
	optmize();
	for (int i = 0; i < opedMidSeq; i++)
		optMid << i << ":" << opedMid[i]->a << opedMid[i]->q1 << opedMid[i]->b << opedMid[i]->q2 << opedMid[i]->c << opedMid[i]->q3 << opedMid[i]->d << opedMid[i]->q4 << opedMid[i]->e << endl;
	for (int i = 0; i < blockNum; i++) {
		optBlock << i << ":" << blockArray[i]->start << "  " << blockArray[i]->end << "  " << blockArray[i]->Next << "  " << blockArray[i]->jumpNext << "  " << endl;
	}
	makeAsm();
	/*
			  **/
	return 0;
}
