#include <iostream>
#include <vector>
#include <chrono>
#include <time.h> 
#include <boost/random/random_device.hpp>
#include <boost/multiprecision/cpp_int.hpp> 
#include <boost/random.hpp>
#include <sstream>
#include <fstream>
#include <unordered_map>
#include <string>
#include <map>
#include <unordered_set>

using namespace std;
using namespace boost::multiprecision;
using namespace boost::random;

cpp_int pSize;

cpp_int generate_random(cpp_int a, cpp_int b) {
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<cpp_int> dist(a, b);
    return dist(gen);
}

cpp_int rand_large_by_bit_length(int l) {
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<int> distribution(0, 1);
    cpp_int result = 0;
    for (int i = 1; i < l - 1; ++i) {
        result <<= 1;
        result += distribution(gen);
    }
    result |= (cpp_int(1) << (l - 1));
    result |= 1;
    return result;
}

cpp_int powMod(cpp_int x, cpp_int n, cpp_int m) {
    cpp_int N = n, Y = 1, Z = x % m;
    while (N != 0) {
        cpp_int lastN = N % 2;
        N = N / 2;
        if (lastN == 0) {
            Z = (Z * Z) % m;
            continue;
        }
        Y = (Y * Z) % m;
        if (N == 0)
            break;
        Z = (Z * Z) % m;
    }
    return Y % m;
}


cpp_int nod(cpp_int a, cpp_int m) {
    if (m == 0)
        return a;
    else
        return nod(m, a % m);
}

cpp_int algEuclidExtended(cpp_int a, cpp_int b, cpp_int& x, cpp_int& y) {
    if (a == 0) {
        x = 0;
        y = 1;
        return b;
    }
    cpp_int xi, yi;
    cpp_int nod = algEuclidExtended(b % a, a, xi, yi);
    x = yi - (b / a) * xi;
    y = xi;
    return nod;
}

string findInStr(string const& str, int n) {
    if (str.length() < n)
        return str;
    return str.substr(0, n);
}

vector<string> splitString(const string& input, char zn) {
    istringstream stream(input);
    string str1;
    vector<string> strs;
    while (getline(stream, str1, zn)) {
        strs.push_back(str1);
    }
    return strs;
}

void helpFunc() {
    cout << "Введена команда c /h. Допустимые параметры:";
    cout << "\n\n/n:<n> - Число сторон n, между которыми нужно разделить секрет";
    cout << "\n\n/k:<k> - Число сторон k, необходимых для восстановления секрета";
    cout << "\n\n/m:<m> - Режим работы - gen (режим разделения секрета) или rec (режим восстановления секрета)";
    cout << "\n\n/l:<l> - Модуль для последовательности Миньотта";
    cout << "\n\n/input:<filename> - Файл с входными данными для восстановления секрета.";
    cout << "\n\n/output:<filename> - Файл, куда будет записываться результат работы программы.";
    cout << "\n\n/h – информация о допустимых параметрах командной строки программы.\n";
}



//Решение системы линейных сравнений c помощью Греко-Китайской теоремы
cpp_int ChinaXi(vector <pair <cpp_int, cpp_int>> congruences, int k) { // r_i a_i
    vector <cpp_int> m_i(k);
    vector <cpp_int> d_i(k);
    cpp_int M = 1;
    for (int i = 0; i < k; i++) {
        cpp_int a_i = congruences[i].second;
        M *= a_i;
    }
    for (int i = 0; i < k; i++) {
        cpp_int a_i = congruences[i].second;
        m_i[i] = M / a_i;
        cpp_int x, y;
        algEuclidExtended(m_i[i], a_i, x, y);
        if (x < 0)
            x += a_i;
        d_i[i] = x;
    }
    cpp_int u = 0;
    for (int i = 0; i < k; i++) {
        u += m_i[i] * d_i[i] * congruences[i].first;
        u %= M;
        if (u < 0)
            u += M;
    }
    return u;
}

bool isGoodSequence(vector <cpp_int> minyottSequence, cpp_int k, cpp_int n, cpp_int &firstMult, cpp_int &secondMult) {
    firstMult = 1;
    secondMult = 1;
    for (int i = 0; i < k - 1; i++)
        firstMult *= minyottSequence[(int)n - 1 - i];

    for (int i = 0; i < k; i++)
        secondMult *= minyottSequence[i];

    if (firstMult < secondMult)
        return true;
    return false;
}

void findMinyottSequence(vector <cpp_int>& minyottSequence, cpp_int k, cpp_int n, cpp_int modSequence, cpp_int& firstMult, cpp_int& secondMult) {
    while (true) {
        minyottSequence.clear();
        for (int i = 0; i < n; i++) {
            while (true) {
                cpp_int p_i = generate_random(2, modSequence);
                bool nodNot1 = false;
                for (int j = 0; j < minyottSequence.size(); j++) {
                    if (nod(p_i, minyottSequence[j]) != 1) {
                        nodNot1;
                        nodNot1 = true;
                    }
                }
                if (!nodNot1) {
                    minyottSequence.push_back(p_i);
                    break;
                }
            }
        }
        sort(minyottSequence.begin(), minyottSequence.end());
        if (isGoodSequence(minyottSequence, k, n, firstMult, secondMult))
            break;
    }
    return;
}

void minyott_gen(cpp_int k, cpp_int n, const string& output, cpp_int modSequence) {

    vector <cpp_int> minyottSequence;
    cpp_int beta, alpha;
    findMinyottSequence(minyottSequence, k, n, modSequence, beta, alpha);

    cpp_int S = generate_random(beta + 1, alpha - 1);

    ofstream outFile(output, ios::out | ios::trunc);
    if (!outFile.is_open()) {
        cerr << "Ошибка открытия файла\n";
        return;
    }
    outFile << "Секрет: " << S << "\n";
    outFile << "Для восстановления секрета нужно " << k << " участников\n\n";

    outFile << "Системы уравнений (x = b_i mod m_i), представленная в виде вида b_i m_i : "<< "\n";
    for (int i = 0; i < n; i++) {
        outFile << S % minyottSequence[i] << " " << minyottSequence[i] << "\n";
    }

    outFile.close();

    return;
}

void getCongruences(vector<pair<cpp_int, cpp_int>> &congruences, const string& input) {
    ifstream inputFile(input);
    if (!inputFile.is_open()) {
        cerr << "Ошибка открытия файла\n";
        return;
    }

    cpp_int a, b;
    while (inputFile >> a >> b) {
        congruences.push_back(make_pair(a, b));
    }

    inputFile.close();
}
void minyott_rec(const string& input, const string& output, cpp_int k) {

    vector<pair<cpp_int, cpp_int>> congruences;
    getCongruences(congruences, input);
    if (congruences.size() < k) {
        cout << "\n Количество уравнений должно быть больше либо равно " << k << "\n";
        return;
    }
    cpp_int S = ChinaXi(congruences, (int)k);

    ofstream outFile(output, ios::out | ios::trunc);
    if (!outFile.is_open()) {
        cerr << "Ошибка открытия файла\n";
        return;
    }

    outFile << "Секрет: " << S << "\n";

    outFile.close();
    return;
}

int main(int argc, char* argv[]) {
    setlocale(LC_ALL, "rus");
    string mode = "gen";
    string input = "null", output = "null";
    cpp_int k = 0;
    cpp_int n = 0;
    cpp_int modSequence = 10000;
    for (int i = 0; argv[i]; i++) {
        string checkStr = string(argv[i]);
        if (findInStr(checkStr, 2) == "/h") {
            helpFunc();
            return 0;
        }
        if (checkStr.length() > 2) {
            string ifStr = findInStr(checkStr, 3);
            string ifStr2 = findInStr(checkStr, 7);
            string ifStr3 = findInStr(checkStr, 8);
            char symbol = ',';
            if (ifStr == "/n:") { //разделить между n сторонами
                n = stoi(checkStr.substr(3, checkStr.length()));

            }
            if (ifStr == "/k:") { //k - кол-во для восстановления
                k = stoi(checkStr.substr(3, checkStr.length()));
            }
            if (ifStr == "/m:") { //режим gen или rec
                mode = checkStr.substr(3, checkStr.length());
            }
            if (ifStr == "/l:") { //модуль для последовательности Миньотта
                modSequence = stoi(checkStr.substr(3, checkStr.length()));
            }
            if (ifStr2 == "/input:") {
                input = checkStr.substr(7, checkStr.length());
            }
            if (ifStr3 == "/output:") {
                output = checkStr.substr(8, checkStr.length());
            }
        }
    }
    if (mode == "gen") {
        if (k == 0 || n == 0 || output == "null") {
            cout << "\n Не хватает параметров \n";
            return 0;
        }
        if (n < 2) {
            cout << "\n n < 2 \n";
            return 0;
        }
        if (k < 2) {
            cout << "\n k < 2 \n";
            return 0;
        }
        if (k > n) {
            cout << "\n k > n \n";
            return 0;
        }
        minyott_gen(k, n, output, modSequence);
        return 0;
    }
    if (mode == "rec") {
        if (input == "null" || output == "null" || k == 0) {
            cout << "\n Не хватает параметров \n";
            return 0;
        }
        minyott_rec(input, output, k);
        return 0;
    }
    return 0;
}