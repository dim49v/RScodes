#include <iostream>
#include <fstream>
#include <time.h>
#include <vector>
#include <math.h>

using namespace std;

int monde;
int n;
int t;
int d;
int k;

int* p; // простой многочлен, например [1, 0, 1, 0, 0, 1]
int* a;
int* g; // порождающий многочлен
int* g_root; // корни порождающего многочлена
int* res;
int* index_a;

const int min_error_prob_lg = -2;
const int max_error_prob_lg = 0;
const float error_prob_lg_step = 0.05;

int GFsum(int b, int c) {
	return b ^ c;
}

int GFmul(int b, int c) {
	int sum;
	if (b == 0 || c == 0) return 0;
	sum = (index_a[b] + index_a[c]) % n;
	return a[sum];
}

int GFdiv(int b, int c) {
	int sum;
	if (b == 0) return 0;
	if (c == 0) return -1;
	sum = (index_a[b] - index_a[c] + n) % n;
	return a[sum];
}

void init() {
	cout << "n (code length): ";
	cin >> n;
	cout << "t (errors count): ";
	cin >> t;
	d = 2 * t;
	k = n - d;
	cout << "RS(" << n << "," << k << ")" << endl;
	cout << "Degree of a simple polynomial: ";
	cin >> monde;
	p = new int[monde + 1];
	for (int i = 0; i <= monde; i++) {
		cout << "X" << monde - i << ": ";
		cin >> p[i];
	}
	index_a = new int[n + 1];
	a = new int[n + 1]; 
	g = new int[d + 1]{ 0 };
	g_root = new int[d];
	res = new int[n];

	int mask = 1;
	a[monde] = 0;
	for (int i = 0; i < monde; i++)
	{
		a[i] = mask;
		index_a[a[i]] = i;
		if (p[i] != 0) {
			a[monde] ^= mask;
		}
		mask <<= 1;
	}
	index_a[a[monde]] = monde;
	mask >>= 1;
	for (int i = monde + 1; i < n; i++)
	{
		if (a[i - 1] >= mask) {// (..., 1) | (..., 0)
			a[i] = a[monde] ^ ((a[i - 1] ^ mask) << 1); // (..., 1) => (..., 0) * a + a[monde], 
		}
		else {
			a[i] = a[i - 1] << 1; // (..., 0) => (..., 0) * a
		}
		index_a[a[i]] = i;
	}
	index_a[0] = -1;
	a[n] = 0;
}

void polynomial(int b) {
	g[0] = a[b];
	g[1] = a[0];
	for (int i = b + 1; i < n - k + b; i++) {
		for (int u = i; u >= b; u--) {
			g[u] = GFsum(g[u - 1], GFmul(g[u], a[i % n]));
		}
		g[0] = GFmul(g[0], a[i % n]);
	}
	int temp;
	for (int i = 0; i < d; i++) {
		g_root[i] = a[i + b];
	}
}

void encode(int* inf) {
	int* mas = new int[n] { 0 };
	for (int i = 0; i < k; i++) {
		mas[i + d] = inf[i];
	}
	int q = 0;
	for (int i = n - 1; i >= d; i--) {
		q = GFdiv(mas[i], g[d]);
		for (int u = 0; u <= d; u++) {
			mas[i - u] = GFsum(mas[i - u], GFmul(g[d - u], q));
		}
	}
	for (int i = d; i < n; i++) {
		res[i] = inf[i - d];
	}
	for (int i = 0; i < d; i++) {
		res[i] = mas[i];
	}
	delete[] mas;
}

void GetMatrixMinnor(int** mas, int** p, int i, int j, int m) {
	int ki, kj, di, dj;
	di = 0;
	for (ki = 0; ki < m - 1; ki++) {
		if (ki == i) di = 1;
		dj = 0;
		for (kj = 0; kj < m - 1; kj++) {
			if (kj == j) dj = 1;
			p[ki][kj] = mas[ki + di][kj + dj];
		}
	}
}

int Determinant(int** mas, int m) {
	int i, j, d, n;
	int** p;
	p = new int* [m];
	for (i = 0; i < m; i++)
		p[i] = new int[m];
	j = 0; d = 0;
	n = m - 1;
	if (m < 1) cout << "The determinant cannot be calculated!";
	if (m == 1) {
		d = mas[0][0];
		return d;
	}
	if (m == 2) {
		d = GFsum(GFmul(mas[0][0], mas[1][1]), GFmul(mas[1][0], mas[0][1]));
		return d;
	}
	if (m > 2) {
		for (i = 0; i < m; i++) {
			GetMatrixMinnor(mas, p, i, 0, m);
			d = GFsum(d, GFmul(mas[i][0], Determinant(p, n)));
		}
	}
	return d;
}

int** InverseMatrix(int** matr, int m, int det) {
	int** newMatr = new int* [m];
	for (int i = 0; i < m; i++) {
		newMatr[i] = new int[m];
	}
	int** tmpMatr = new int* [m];
	for (int i = 0; i < m; i++) {
		tmpMatr[i] = new int[m];
	}
	int invDet = GFdiv(1, det);
	if (m == 1) {
		newMatr[0][0] = invDet;
	}
	else {
		for (int i = 0; i < m; i++) {
			for (int u = 0; u < m; u++) {
				GetMatrixMinnor(matr, tmpMatr, i, u, m);
				newMatr[u][i] = GFmul(invDet, Determinant(tmpMatr, m - 1));
			}
		}
	}

	return newMatr;
}

int* decode_PGZ(bool &fail) {
	int* mas = new int[n];
	for (int i = 0; i < n; i++) {
		mas[i] = res[i];
	}
	int* s = new int[d] { 0 };
	int sum;
	// синдром ошибки
	for (int i = 0; i < d; i++) {
		int q = 1;
		sum = 0;
		for (int u = 0; u < n; u++) {
			sum = GFsum(sum, GFmul(res[u], q));
			q = GFmul(q, g_root[i]);
		}
		s[i] = sum;
	}
	// количество ошибок
	int v = t + 1;
	int det = 0;
	int** matr = new int* [v];
	do {
		--v;
		if (v > 0) {
			matr = new int* [v];
			for (int i = 0; i < v; i++) {
				matr[i] = new int[v];
				for (int u = 0; u < v; u++) {
					matr[i][u] = s[i + u];
				}
			}
			det = Determinant(matr, v);
		}
	} while (det == 0 && v > 0);
	if (v == 0) {
		return mas;
	}
	// многочлен локаторов ошибок
	int** invMatr = InverseMatrix(matr, v, det);
	int* L = new int[v];
	int* X = new int[v];
	for (int i = 0; i < v; i++) {
		sum = 0;
		for (int u = 0; u < v; u++) {
			sum = GFsum(sum, GFmul(invMatr[i][u], s[v + u]));
		}
		L[i] = sum;
	}
	// корни многочлена локаторов ошибок -> локаторы ошибок
	int y = 0;
	for (int i = 1; i <= n; i++) {
		int q = i;
		sum = 1;
		for (int u = v - 1; u >= 0; u--) {
			sum = GFsum(sum, GFmul(L[u], q));
			q = GFmul(q, i);
		}
		if (sum == 0) {
			X[y++] = GFdiv(1, i);
		}
	}
	if (y < v) {
		fail = true;
		return mas;
	}
	// величины ошибок
	matr = new int* [v];
	int* X2 = new int[v];
	for (int i = 0; i < v; i++) {
		X2[i] = X[i];
	}
	for (int i = 0; i < v; i++) {
		matr[i] = new int[v];
		for (int u = 0; u < v; u++) {
			matr[i][u] = X2[u];
			X2[u] = GFmul(X2[u], X[u]);
		}
	}
	det = Determinant(matr, v);
	invMatr = InverseMatrix(matr, v, det);
	L = new int[v];
	for (int i = 0; i < v; i++) {
		sum = 0;
		for (int u = 0; u < v; u++) {
			sum = GFsum(sum, GFmul(invMatr[i][u], s[u]));
		}
		L[i] = sum;
		mas[det] = y;
	}

	return mas;
}

int* decode_Euclid(bool &fail) {
	int* mas = new int[n];
	for (int i = 0; i < n; i++) {
		mas[i] = res[i];
	}
	int sum;
	int* S = new int[d] { 0 };
	// синдром ошибки
	for (int i = 0; i < d; i++) {
		int q = 1;
		sum = 0;
		for (int u = 0; u < n; u++) {
			sum = GFsum(sum, GFmul(mas[u], q));
			q = GFmul(q, g_root[i]);
		}
		S[i] = sum;
	}
	int* s = new int[d + 1]{ 0 };
	s[d] = 1;
	int* tt = new int[d + 1]{ 0 };
	for (int i = 0; i < d; i++) {
		tt[i] = S[i];
	}
	delete[] S;
	int* A11 = new int[d + 1]{ 0 };
	int* A12 = new int[d + 1]{ 0 };
	int* A21 = new int[d + 1]{ 0 };
	int* A22 = new int[d + 1]{ 0 };
	A11[0] = 1;
	A22[0] = 1;
	bool degT = false;
	for (int i = d; i >= t; i--) {
		if (!degT && tt[i] != 0) {
			degT = true;
		}
	}
	int* A11_ = new int[d + 1]{ 0 };
	int* A12_ = new int[d + 1]{ 0 };
	int* A21_ = new int[d + 1]{ 0 };
	int* A22_ = new int[d + 1]{ 0 };
	// НОД
	while (degT) {
		int* sCopy = new int[d + 1]{ 0 };
		for (int i = 0; i <= d; i++) {
			sCopy[i] = s[i];
		}
		int degt = d, degs = d;
		while (tt[degt] == 0) { degt--; }
		while (sCopy[degs] == 0) { degs--; }
		int y = degs - degt;
		int* Q = new int[d + 1]{ 0 };
		int q;
		for (int i = 0; i <= y; i++) {
			q = GFdiv(sCopy[degs - i], tt[degt]);
			if (q != 0) {
				for (int u = 0; u <= degt; u++) {
					sCopy[degs - i - u] = GFsum(sCopy[degs - i - u], GFmul(tt[degt - u], q));
				}
			}
			Q[y - i] = q;
		}
		// sCopy = s % tt
		// {s(x), t(x)} = [[0,1],[1,-Q(X)]] * {s(x), t(x)}
		for (int i = 0; i <= d; i++) {
			s[i] = tt[i];
			tt[i] = sCopy[i];
		}
		// A(x) = [[0,1],[1,-Q(X)]]*A(x)
		for (int i = 0; i <= d; i++) {
			A11_[i] = A21[i];
			A12_[i] = A22[i];
			A21_[i] = A11[i];
			A22_[i] = A12[i];
		}
		for (int i = 0; i <= d; i++) {
			for (int u = 0; i + u <= d; u++) {
				A21_[i + u] = GFsum(A21_[i + u], GFmul(Q[i], A21[u]));
			}
		}
		for (int i = 0; i <= d; i++) {
			for (int u = 0; i + u <= d; u++) {
				A22_[i + u] = GFsum(A22_[i + u], GFmul(Q[i], A22[u]));
			}
		}
		for (int i = 0; i <= d; i++) {
			A11[i] = A11_[i];
			A12[i] = A12_[i];
			A21[i] = A21_[i];
			A22[i] = A22_[i];
		}
		degT = false;
		for (int i = d; i >= t; i--) {
			if (!degT && tt[i] != 0) {
				degT = true;
			}
		}
		delete[] sCopy;
		delete[] Q;
	}
	// tt - многочлен значений ошибок
	// A22 - многочлен локаторов ошибок
	// нормализация
	int delta = A22[0];
	int* W = new int[d + 1];
	int* L = new int[d + 1];
	for (int i = 0; i <= d; i++) {
		W[i] = GFdiv(tt[i], delta);
		L[i] = GFdiv(A22[i], delta);
	}
	// нахождение кореней многочлена локаторов ошибок -> локаторы ошибок
	int v = d;
	while (L[v] == 0) { v--; }
	int* X = new int[d]{ 0 };
	int y = 0;
	for (int i = 1; i <= n; i++) {
		int q = i;
		sum = L[0];
		for (int u = 1; u <= v; u++) {
			sum = GFsum(sum, GFmul(L[u], q));
			q = GFmul(q, i);
		}
		if (sum == 0) {
			if (y < d) {
				X[y++] = GFdiv(1, i);
			}
		}
	}
	if (y < v || v > t) {
		fail = true;
		delete[] A11;
		delete[] A12;
		delete[] A21;
		delete[] A22;
		delete[] A11_;
		delete[] A12_;
		delete[] A21_;
		delete[] A22_;
		delete[] s;
		delete[] tt;
		delete[] L;
		delete[] W;
		delete[] X;
		return mas;
	}
	// формальная производная многочлена локаторов ошибок
	for (int i = 1; i <= v; i++) {
		y = 0;
		for (int u = 0; u < i; u++) {
			y = GFsum(y, L[i]);
		}
		L[i - 1] = y;
	}
	L[v] = 0;
	int W_, L_, q, idx, val;
	// величины ошибок
	for (int i = 0; i < v; i++) {
		W_ = W[0];
		L_ = L[0];
		q = GFdiv(1, X[i]);
		for (int u = 1; u <= v; u++) {
			W_ = GFsum(W_, GFmul(W[u], q));
			L_ = GFsum(L_, GFmul(L[u], q));
			q = GFdiv(q, X[i]);
			if (W_ < 0 || L_ < 0) {
				fail = true;
				delete[] A11;
				delete[] A12;
				delete[] A21;
				delete[] A22;
				delete[] A11_;
				delete[] A12_;
				delete[] A21_;
				delete[] A22_;
				delete[] s;
				delete[] tt;
				delete[] L;
				delete[] W;
				delete[] X;
				return mas;
			}
		}
		idx = index_a[X[i]];
		
		val = GFsum(GFdiv(W_, L_), mas[index_a[X[i]]]);
		mas[idx] = val;
	}
	delete[] A11;
	delete[] A12;
	delete[] A21;
	delete[] A22;
	delete[] A11_;
	delete[] A12_;
	delete[] A21_;
	delete[] A22_;
	delete[] s;
	delete[] tt;
	delete[] L;
	delete[] W;
	delete[] X;

	return mas;
}
void generateInfo(int* inf) {
	for (int i = 0; i < k; i++) {
		inf[i] = rand() % (n + 1);
	}
}

void makeError(int* data, double prob) {
	for (int i = 0; i < n; i++) {
		if ((double)rand() / RAND_MAX < prob) {
			data[i] = (data[i] + (rand() % (n-1) + 1)) % n;
		}
	}
}

int main() {
	ofstream fout;
	fout.open("result.txt");
	srand(time(0));
	init();
	cout << "i" << '\t' << "a[i]" << '\t' << "index_a[i]" << endl;
	for (int i = 0; i <= n; i++) {
		cout << i << '\t' << a[i] << '\t' << index_a[i] << endl;
	}
	int* data = new int[k] { 0 }; //информационные символы
	polynomial(1);
	bool fail;
	int failCount;
	int* decodeRes = new int[n];
	int* encodeRes = new int[n];
	int m;
	cout << "Number of iterations: ";
	cin >> m;
	int last = 0;
	double prob;
	for (double probLg = min_error_prob_lg; probLg <= max_error_prob_lg; probLg += error_prob_lg_step) {
		prob = pow(10, probLg);
		failCount = 0;
		for (int i = 0; i < m; i++) {
			generateInfo(data);
			encode(data);
			for (int u = 0; u < n; u++) {
				encodeRes[u] = res[u];
			}
			// внесение ошибок
			makeError(res, prob);
			fail = false;

			decodeRes = decode_Euclid(fail);
			//decodeRes = decode_PGZ(fail);

			for (int u = 0; u < n && !fail; u++) {
				if (decodeRes[u] != encodeRes[u]) {
					fail = true;
				}
			}
			if (fail) {
				failCount++;
			}
			delete[] decodeRes;
		}
		fout << probLg << '\t' << (double)(failCount) / m << '\n';
		cout << probLg << '\t' << (double)(failCount) / m << '\n';
	}
	fout.close();
	cout << '\n';
}