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
#include <windows.h>
#include <cryptlib.h>
#include "rijndael.h"
#include "modes.h"
#include "files.h"
#include "osrng.h"
#include "hex.h"
#include <unordered_set>

using namespace std;
using namespace boost::multiprecision;
using namespace boost::random;
using namespace CryptoPP;

const int AES_KEY_SIZE = AES::DEFAULT_KEYLENGTH;
const int AES_BLOCK_SIZE = AES::BLOCKSIZE;
cpp_int pSize;

cpp_int rand_large(cpp_int w1, cpp_int w2) {
    random_device gen;
    uniform_int_distribution<cpp_int> ui(w1, w2);
    cpp_int y = ui(gen);
    return y;
}

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

bool isPrimeMillerRabin(cpp_int n, cpp_int k) {
    if (n <= 1 || n == 4) return false;
    if (n <= 3) return true;

    cpp_int d = n - 1;
    while (d % 2 == 0)
        d /= 2;

    for (cpp_int i = 0; i < k; i++) {
        cpp_int a = 2 + rand() % (n - 3);
        cpp_int x = powMod(a, d, n);

        if (x == 1 || x == n - 1)
            continue;

        while (d != n - 1) {
            x = (x * x) % n;
            d *= 2;

            if (x == 1) return false;
            if (x == n - 1) break;
        }

        if (x != n - 1) return false;
    }

    return true;
}

string findInStr(string const& str, int n) {
    if (str.length() < n)
        return str;
    return str.substr(0, n);
}

cpp_int min_num_by_l_bits(int l) {
    cpp_int result = 1;
    result |= (cpp_int(1) << (l - 1));
    return result;
}

cpp_int max_num_by_l_bits(int l) {
    cpp_int result = (cpp_int(1) << l) - 1;
    return result;
}

cpp_int generateRandomPrime(int l) {
    cpp_int minNum = min_num_by_l_bits(l);
    cpp_int maxNum = max_num_by_l_bits(l);
    cpp_int randNum = rand_large_by_bit_length(l);
    cpp_int newNum = randNum;
    bool plus1 = true;
    if (newNum % 2 == 0) {
        if (newNum + 1 < maxNum)
            newNum += 1;
        else {
            newNum -= 1;
            plus1 = false;
        }
    }
    randNum = newNum;
    while (!isPrimeMillerRabin(newNum, 20)) {
        if (plus1)
            newNum += 2;
        else
            newNum -= 2;
        if (newNum > maxNum) {
            newNum = randNum;
            plus1 = false;
        }
        if (newNum < minNum) {
            newNum = randNum;
            plus1 = true;
        }
    }
    return newNum;
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

void generate_n(int pLength, int qLength, cpp_int &p, cpp_int &q, cpp_int &n) {
    p = generateRandomPrime(pLength);
    while (!isPrimeMillerRabin(p, 20)) {
        p = generateRandomPrime(pLength);
    }
    q = generateRandomPrime(qLength);
    while (!isPrimeMillerRabin(q, 20)) {
        q = generateRandomPrime(qLength);
    }
    n = p * q;
    return;
}

cpp_int jacobi_symbol(cpp_int a, cpp_int b) {
    if (nod(a, b) != 1)
        return 0;
    else {
        cpp_int r = 1;
        while (a != 0) {
            cpp_int t = 0;
            while (a % 2 == 0) {
                t = t + 1;
                a = a / 2;
            }
            if (t % 2 != 0)
                if (powMod(b, 1, 8) == 3 || powMod(b, 1, 8) == 5)
                    r = r * (-1);
            if (powMod(a, 1, 4) == 3 && powMod(b, 1, 4) == 3)
                r = r * (-1);
            cpp_int c = a;
            if (c != 0)
                a = powMod(b, 1, c);
            b = c;
        }
        return r;
    }
}

void generatePublicKey(cpp_int n, cpp_int p, cpp_int q, cpp_int &peggyPublicKey) {
    while (true) {
        cpp_int v = generate_random(2, n - 2);
        if (nod(v, n) != 1 || jacobi_symbol(v, p) != 1 || jacobi_symbol(v, q) != 1)
            continue;
        cpp_int vSqr = v * v;
        cpp_int phi = (p - 1) * (q - 1);
        cpp_int deg = phi / 2;
        if (powMod(v, deg, n) == 1) {
            peggyPublicKey = v;
            return;
        }
    }
    return;
}

cpp_int normalMod(cpp_int x, cpp_int p) {
    x %= p;
    while (x < 0)
        x += p;
    return x;
}

bool findQM(const cpp_int& p, cpp_int& q, cpp_int& m) {
    if (p <= 1 || p % 2 == 0)
        return false;
    cpp_int k = p - 1;
    m = 0;
    while (k % 2 == 0) {
        k /= 2;
        m++;
    }
    q = k;
    if (nod(q, 2) == 1)
        return true;
    else
        return false;
}

void helpFunc() {
    cout << "Введена команда c /h. Допустимые параметры:";
    cout << "\n\n/t:<t> - количество раундов.";
    cout << "\n\n/pl:<length> - Битовая длина числа p";
    cout << "\n\n/ql:<length> - Битовая длина числа q";
    cout << "\n\n/gg:<round> - Раунд, в который хотим встроиться и изменить данные.";
    cout << "\n\n/h – информация о допустимых параметрах командной строки программы.\n";
}

cpp_int pow2(cpp_int s, cpp_int k) {
    if (k == 0)
        return 1;
    else if (k == 1)
        return s;
    cpp_int s_start = s;
    for (int i = 0; i < k - 1; i++)
        s *= s_start;
    return s;
}

cpp_int func_k_i(cpp_int a_i, cpp_int q, cpp_int p) {
    cpp_int k = 0;
    while (powMod(a_i, pow2(2, k) * q, p) != 1)
        k++;
    return k;
}

cpp_int x_0(cpp_int q, cpp_int p, cpp_int m, cpp_int b, cpp_int a) {
    vector <cpp_int> aVec;
    vector <cpp_int> kVec;
    vector <cpp_int> rVec;
    aVec.push_back(a);
    cpp_int k_i = func_k_i(aVec[0], q, p);
    kVec.push_back(k_i);
    int a_index = 0;
    while (true) {
        cpp_int a_i = aVec[a_index];
        k_i = func_k_i(a_i, q, p);
        if (k_i == 0)
            break;
        if (a_index != 0)
            kVec.push_back(k_i);
        cpp_int a_iB = (a_i * pow2(b, pow2(2, m - k_i))) % p;
        aVec.push_back(a_iB);
        a_index++;
    }
    int n = aVec.size();
    rVec.resize(n);
    rVec[n - 1] = powMod(aVec[n - 1], (q + 1) / 2, p);
    for (int r_i = n - 2; r_i >= 0; r_i--) {
        cpp_int x1, y1;
        cpp_int b_deg = pow2(b, pow2(2, m - kVec[r_i] - 1)) % p; //%p
        algEuclidExtended(b_deg, p, x1, y1);
        if (x1 < 0)
            x1 = x1 + p;
        cpp_int el_obr = x1;
        rVec[r_i] = (rVec[r_i + 1] * el_obr) % p;
    }

    return rVec[0];
}

cpp_int findSqrt(cpp_int p, cpp_int v) {
    cpp_int q, m;
    if (!findQM(p, q, m)) {
        cout << "p - 1 не раскладывается как 2^m * q\n";
        return -1;
    }
    cpp_int b = generate_random(2, p - 1);
    while (jacobi_symbol(b, p) != -1) {
        b = generate_random(2, p - 1);
    }
    cpp_int x0 = x_0(q, p, m, b, v);

    return x0;
}

cpp_int findS(cpp_int x1, cpp_int x2, cpp_int p, cpp_int q, cpp_int n) {
    cpp_int s1 = normalMod(x1, p);
    cpp_int s2 = normalMod(x2, q);
    cpp_int k1, k2;
    algEuclidExtended(p, q, k1, k2);
    if (k1 < 0)
        k1 = k1 + q;
    if (k2 < 0)
        k2 = k2 + p;

    // Используем Китайскую теорему об остатках для нахождения s.
    cpp_int s = (s1 * q * k2 + s2 * p * k1) % n;
    return s;
}

cpp_int findMinS(cpp_int p, cpp_int q, cpp_int n, cpp_int v, cpp_int v_obr) {
    cpp_int v1 = normalMod(v_obr, p);
    cpp_int x1 = findSqrt(p, v1);
    cpp_int v2 = normalMod(v_obr, q);
    cpp_int x2 = findSqrt(q, v2);
    cpp_int s = findS(x1, x2, p, q, n);
    return s;
}


bool FFS_stages(cpp_int p, cpp_int q, cpp_int n, cpp_int  peggyPublicKey, cpp_int peggyPrivateKey, bool hack) {
    
    //ШАГ 1

    cout << "\n\n[Этап 1] ПЕГГИ:\n";

    cpp_int Peggy_r = generate_random(2, n - 1);
    cout << "\n > Сгенерировала случайное число r (r < n) = " << Peggy_r;
    cpp_int r2 = normalMod(normalMod(-Peggy_r, n) * normalMod(-Peggy_r, n), n);
    cpp_int Peggy_x = normalMod(r2, n);
    cout << "\n > Вычислила x = -(r^2) mod n = " << Peggy_x;
    cout << "\n > Отправила x Виктору";
    
    cpp_int Peggy_x_IZM = Peggy_x;
    if (hack) {
        string userCout;
        cout << "\n\nКОНЕЦ ЭТАПА 1. ПРОДОЛЖИТЬ - y, ИЗМЕНИТЬ - i : ";
        cin >> userCout;
        if (userCout == "i") {
            cout << "\n\nx = " << Peggy_x;
            cout << "\n\nМожно изменить: 1 - x";
            cout << "\nВаш выбор: ";
            string userChoiceIzm;
            cin >> userChoiceIzm;
            if (userChoiceIzm == "1") {
                cout << "\n\nВведите новое значение: ";
                cin >> Peggy_x_IZM;
            }
        }
        else if (userCout != "y")
            return false;
    }

    //ШАГ 2

    cout << "\n\n[Этап 2] ВИКТОР:\n";

    cpp_int Victor_x = Peggy_x_IZM;
    cout << "\n > Получил x от Пегги";
    cpp_int Victor_b = generate_random(0, 1);
    cout << "\n > Выбрал случайный бит b = " << Victor_b;
    cout << "\n > Отправил b Пегги";

    cpp_int Victor_b_IZM = Victor_b;
    if (hack) {
        string userCout;
        cout << "\n\nКОНЕЦ ЭТАПА 2. ПРОДОЛЖИТЬ - y, ИЗМЕНИТЬ - i : ";
        cin >> userCout;
        if (userCout == "i") {
            cout << "\n\nx = " << Peggy_x;
            cout << "\n\nМожно изменить: 1 - b";
            cout << "\nВаш выбор: ";
            string userChoiceIzm;
            cin >> userChoiceIzm;
            if (userChoiceIzm == "1") {
                cout << "\n\nВведите новое значение: ";
                cin >> Victor_b_IZM;
            }
        }
        else if (userCout != "y")
            return false;
    }

    //ШАГ 3

    cout << "\n\n[Этап 3] ПЕГГИ:\n";

    cpp_int Peggy_b = Victor_b_IZM;
    cout << "\n > Получила b от Пегги";
    cpp_int forVictor;
    if (Peggy_b == 0) {
        forVictor = Peggy_r;
        cout << "\n > Так как b = 0, отправила Виктору r = " << forVictor;
    }
    else if (Peggy_b == 1) {
        forVictor = normalMod(Peggy_r * peggyPrivateKey, n);
        cout << "\n > Так как b = 1, отправила Виктору y = r * s (mod n) = " << forVictor;
    }
    else {
        cout << "\n > ERROR: b != 0 и b != 1 ";
        return false;
    }

    cpp_int forVictor_IZM = forVictor;
    if (hack) {
        string userCout;
        cout << "\n\nКОНЕЦ ЭТАПА 3. ПРОДОЛЖИТЬ - y, ИЗМЕНИТЬ - i : ";
        cin >> userCout;
        if (userCout == "i") {
            cout << "\n\ny or r = " << forVictor;
            cout << "\n\nМожно изменить: 1 - y or r";
            cout << "\nВаш выбор: ";
            string userChoiceIzm;
            cin >> userChoiceIzm;
            if (userChoiceIzm == "1") {
                cout << "\n\nВведите новое значение: ";
                cin >> forVictor_IZM;
            }
        }
        else if (userCout != "y")
            return false;
    }

    //ШАГ 4

    cout << "\n\n[Этап 4] ВИКТОР:\n";
    cpp_int Victor_4 = forVictor_IZM;
    if (Victor_b == 0) {
        cout << "\n > Получил от Пегги r = " << Victor_4;
        cpp_int rVic = normalMod(normalMod(normalMod(-Victor_4, n) * normalMod(-Victor_4, n), n), n);
        cout << "\n > Проверил выполнение равенства x = -(r^2) mod n: \n\tx = " << Victor_x << "; \n\t-(r^2) mod n = " << rVic;
        if (Victor_x == rVic) {
            cout << "\n > Так как x = -(r^2) mod n, убедился, что Пегги знает значение sqrt(x)";
            return true;
        }
        else {
            cout << "\n > Так как x != -(r^2) mod n, убедился, что Пегги НЕ знает значение sqrt(x)";
            return false;
        }
    }
    else if (Victor_b == 1) {
        cout << "\n > Получил от Пегги y = r * s (mod n) = " << Victor_4;
        cpp_int rVic = normalMod(normalMod(normalMod(Victor_4 * Victor_4, n) * peggyPublicKey, n), n);
        cout << "\n > Проверил выполнение равенства x = y^2 * v (mod n): \n\tx = " << Victor_x << "; \n\ty^2 * v (mod n) = " << rVic;
        if (Victor_x == rVic) {
            cout << "\n > Так как x = y^2 * v (mod n), убедился, что Пегги знает значение sqrt(v^(-1))";
            return true;
        }
        else {
            cout << "\n > Так как x != y^2 * v (mod n), убедился, что Пегги НЕ знает значение sqrt(v^(-1))";
            return false;
        }
    }
    else {
        cout << "\n > ERROR: b != 0 и b != 1 ";
        return false;
    }

}

bool FFS_main(int pLength, int qLength, cpp_int t, cpp_int ggRound) {
    cpp_int p, q, n;
    generate_n(pLength, qLength, p, q, n);
    cpp_int peggyPublicKey;
    generatePublicKey(n, p, q, peggyPublicKey);

    cpp_int x1, y1;
    algEuclidExtended(peggyPublicKey, n, x1, y1);
    if (x1 < 0)
        x1 = x1 + n;
    cpp_int v_obr = x1;
    cpp_int peggyPrivateKey = findMinS(p, q, n, peggyPublicKey, v_obr);
    cout << "\nСгенерированные параметры:\n";
    cout << "\np = " << p << "\n";
    cout << "\nq = " << q << "\n";
    cout << "\nn = " << n << "\n";
    int bit_count = msb(n) + 1;
    cout << "\nКоличество битов в числе n: " << bit_count << "\n";
    cout << "\nv = " << peggyPublicKey << "\n";
    cout << "\ns = " << peggyPrivateKey << "\n";
    cpp_int rounds = 1;
    cpp_int true_rounds = 0;
    while (rounds != t + 1) {
        bool hack = false;
        cout << "\n\n\n\t\tРАУНД " << rounds << " ИЗ " << t << "\n\n\n";
        if (rounds == ggRound)
            hack = true;
        if (FFS_stages(p, q, n, peggyPublicKey, peggyPrivateKey, hack)) {
            cout << "\n\nРЕЗУЛЬТАТ ВЫПОЛНЕНИЯ ПРОТОКОЛА В " << rounds << " РАУНДЕ: TRUE\n";
            true_rounds++;
        }
        else
            cout << "\n\nРЕЗУЛЬТАТ ВЫПОЛНЕНИЯ ПРОТОКОЛА В " << rounds << " РАУНДЕ: FALSE\n";
        rounds++;
    }
    cout << "\n\nПройдено " << true_rounds << " раундов из " << t << "\n";
    return true;
}

int main(int argc, char* argv[]) {
    setlocale(LC_ALL, "rus");
    int lenP = 0, lenQ = 0, t = 0;
    cpp_int ggRound = 0;
    for (int i = 0; argv[i]; i++) {
        string checkStr = string(argv[i]);
        if (findInStr(checkStr, 2) == "/h") {
            helpFunc();
            return 0;
        }
        if (checkStr.length() > 2) {
            string ifStr = findInStr(checkStr, 3);
            char symbol = ',';
            if (ifStr == "/t:") {
                t = stoi(checkStr.substr(3, checkStr.length()));
            }
            if (ifStr == "/pl") {
                lenP = stoi(checkStr.substr(4, checkStr.length()));
            }
            if (ifStr == "/ql") {
                lenQ = stoi(checkStr.substr(4, checkStr.length()));
            }
            if (ifStr == "/gg") {
                ggRound = stoi(checkStr.substr(4, checkStr.length()));
            }
        }
    }

    FFS_main(lenP, lenQ, t, ggRound);

    return 0;
}