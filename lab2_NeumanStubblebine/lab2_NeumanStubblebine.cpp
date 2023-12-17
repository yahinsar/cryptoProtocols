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
#include <ctime>

using namespace std;
using namespace boost::multiprecision;
using namespace boost::random;
using namespace CryptoPP;

const int AES_KEY_SIZE = AES::DEFAULT_KEYLENGTH;
const int AES_BLOCK_SIZE = AES::BLOCKSIZE;

string byteArrayToHexString(const byte* input, size_t length) {
    ostringstream ss;
    ss << hex << setfill('0');
    for (size_t i = 0; i < length; ++i)
        ss << setw(2) << static_cast<int>(input[i]);
    return ss.str();
}

string encryptAES(const string& plainText, const string& hexKey) {
    SecByteBlock key((const byte*)hexKey.data(), AES_BLOCK_SIZE);
    ECB_Mode<AES>::Encryption encryptor;
    encryptor.SetKey(key, key.size());
    string cipherText;
    StringSource(plainText, true, new StreamTransformationFilter(encryptor, new StringSink(cipherText)));
    return cipherText;
}

string decryptAES(const string& cipherText, const string& hexKey) {
    SecByteBlock key((const byte*)hexKey.data(), AES_BLOCK_SIZE);
    ECB_Mode<AES>::Decryption decryptor;
    decryptor.SetKey(key, key.size());
    string decryptedText;
    StringSource(cipherText, true, new StreamTransformationFilter(decryptor, new StringSink(decryptedText)));
    return decryptedText;
}

string generateRandomHexKey(int keySize) {
    AutoSeededRandomPool prng;
    SecByteBlock key(keySize);
    prng.GenerateBlock(key, keySize);
    string hexKey;
    HexEncoder encoder(new StringSink(hexKey));
    encoder.Put(key, keySize);
    encoder.MessageEnd();
    return hexKey;
}

string findInStr(string const& str, int n) {
    if (str.length() < n)
        return str;
    return str.substr(0, n);
}

string getTimestamp() {
    time_t currentTime = time(nullptr);
    tm timeInfo = {};
    localtime_s(&timeInfo, &currentTime);
    char buffer[80];
    strftime(buffer, 80, "%Y-%m-%d %H:%M:%S", &timeInfo);
    string timestamp(buffer);
    return timestamp;
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

cpp_int rand_large_by_bit_length(int bit_length) {
    random_device gen;
    uniform_int_distribution<int> ui(0, 1);
    cpp_int result = 0;
    for (int i = 0; i < bit_length; ++i) {
        result <<= 1;
        result |= ui(gen);
    }
    return result;
}

void helpFunc() {
    cout << "Введена команда c /h. Допустимые параметры:";
    cout << "\n\n/p:<p> - битовая длина случайных чисел Ra и Rb, генерируемых Алисой и Бобом соответственно (по умолчанию: 128).";
    cout << "\n\n/2e – Алисе и Бобу повторно проверить подлинность друг друга, не обращаясь к Тренту.";
    cout << "\n\n/h – информация о допустимых параметрах командной строки программы.\n";
}

bool NeumanStubblebineVerification(int p, bool oneMoreVerification) {
    char zn = ',';
    cout << "\nДемонстрация работы протокола \"Ньюмана-Стабблбайна\"\n\n";

    //Ключи:
    const string BobTrentHexKey = generateRandomHexKey(AES_KEY_SIZE);
    cout << "\nBob & Trent AES key: " << BobTrentHexKey;
    const string AliceTrentHexKey = generateRandomHexKey(AES_KEY_SIZE);
    cout << "\nAlice & Trent AES key: " << AliceTrentHexKey;

    //АЛИСА

    cout << "\n\n[Этап 1] АЛИСА:\n";

    cpp_int r_a = rand_large_by_bit_length(p);
    string name_a = "Alice";
    string str_r_a = boost::lexical_cast<string>(r_a);
    cout << "\n > Сгенерировала случайное число Ra = " << str_r_a;
    string alice_first_str = name_a + "," + str_r_a;
    cout << "\n > Объединила свое имя с числом Ra: " << alice_first_str << " и отправила данное сообщение Бобу";


    //БОБ

    cout << "\n\n[Этап 2] БОБ:\n";

    cout << "\n > Получил сообщение Алисы : " << alice_first_str;
    vector<string> alice_first_str_vec = splitString(alice_first_str, zn);
    string BZ_name_a = alice_first_str_vec[0];
    string BZ_r_a = alice_first_str_vec[1];
    cout << "\n > Узнал:\n    имя Алисы A: " << BZ_name_a << ";\n    случайное число Алисы Ra: " << BZ_r_a;
    string t_b = getTimestamp();
    string bob_first_str = alice_first_str + "," + t_b;
    cout << "\n > Объединил имя Алисы, ее случайное число и метку времени: " << bob_first_str;
    //2023-10-10 18:26:03
    string e_b = encryptAES(bob_first_str, BobTrentHexKey);
    cout << "\n > Зашифровал данное сообщение ключом (Bob & Trent): " << byteArrayToHexString(reinterpret_cast<const byte*>(e_b.data()), e_b.length());
    string name_b = "Bob";
    cpp_int r_b = rand_large_by_bit_length(p);
    string str_r_b = boost::lexical_cast<string>(r_b);
    cout << "\n > Сгенерировал случайное число Rb = " << str_r_b;
    vector <string> bob_first_str_vec = { name_b, str_r_b, e_b };
    cout << "\n > Объединил свое имя с числом Rb и зашифрованным сообщением и отправил данное сообщение Тренту";

    //ТРЕНТ

    cout << "\n\n[Этап 3] ТРЕНТ:\n";

    cout << "\n > Получил сообщение Боба";
    string TZ_name_b = bob_first_str_vec[0];
    string TZ_r_b = bob_first_str_vec[1];
    string TZ_e_b = bob_first_str_vec[2];
    vector <string> TZ_e_b_decrypted_vec = splitString(decryptAES(TZ_e_b, BobTrentHexKey), zn);
    string TZ_name_a = TZ_e_b_decrypted_vec[0];
    string TZ_r_a = TZ_e_b_decrypted_vec[1];
    string TZ_t_b = TZ_e_b_decrypted_vec[2];
    cout << "\n > Узнал:\n    имя Боба B: " << TZ_name_b << ";\n    случайное число Боба Rb: " << TZ_r_b << ";\n    имя Алисы A: " << TZ_name_a << ";\n    случайное число Алисы Ra: " << TZ_r_a << ";\n    временную метку Боба Tb: " << TZ_t_b;
    const string SessionKey = generateRandomHexKey(AES_KEY_SIZE);
    cout << "\n > Сгенерировал случайный сессионный ключ K = " << SessionKey;

    string trent_first_str = TZ_name_b + "," + TZ_r_a + "," + SessionKey + "," + TZ_t_b;
    cout << "\n > Создал первое сообщение (B, Ra, K, Tb): " << trent_first_str;
    string e_a = encryptAES(trent_first_str, AliceTrentHexKey);
    cout << "\n > Зашифровал первое сообщение ключом (Alice & Trent): " << byteArrayToHexString(reinterpret_cast<const byte*>(e_a.data()), e_a.length());

    string trent_second_str = TZ_name_a + "," + SessionKey + "," + TZ_t_b;
    cout << "\n > Создал второе сообщение (A, K, Tb): " << trent_second_str;
    e_b = encryptAES(trent_second_str, BobTrentHexKey);
    cout << "\n > Зашифровал второе сообщение ключом (Bob & Trent): " << byteArrayToHexString(reinterpret_cast<const byte*>(e_b.data()), e_b.length());
    vector <string> trent_strs_vec = { e_a , e_b, TZ_r_b };
    cout << "\n > Отправил Алисе два сообщения и Rb";

    //АЛИСА

    cout << "\n\n[Этап 4] АЛИСА:\n";

    cout << "\n > Получила сообщения Трента: ";
    string AZ_trent_first_str = trent_strs_vec[0];
    cout << "\n    Первое сообщение Трента: " << byteArrayToHexString(reinterpret_cast<const byte*>(AZ_trent_first_str.data()), AZ_trent_first_str.length());
    string AZ_trent_second_str = trent_strs_vec[1];
    cout << "\n    Второе сообщение Трента: " << byteArrayToHexString(reinterpret_cast<const byte*>(AZ_trent_second_str.data()), AZ_trent_second_str.length());
    string AZ_r_b = trent_strs_vec[2];
    cout << "\n    Случайное число Боба Rb: " << AZ_r_b;
    vector <string> AZ_trent_first_str_decrypted_vec = splitString(decryptAES(AZ_trent_first_str, AliceTrentHexKey), zn);
    string AZ_b_name = AZ_trent_first_str_decrypted_vec[0];
    string AZ_r_a = AZ_trent_first_str_decrypted_vec[1];
    string AZ_K = AZ_trent_first_str_decrypted_vec[2];
    string AZ_t_b = AZ_trent_first_str_decrypted_vec[3];
    cout << "\n > Расшифровала первое сообщение Трента и узнала:";
    cout << "\n    Имя Боба B: " << AZ_b_name;
    cout << "\n    Случайное число Алисы Ra: " << AZ_r_a;
    cout << "\n    Сеансовый ключ K: " << AZ_K;
    cout << "\n    Временную метку Боба Tb: " << AZ_t_b;

    if (str_r_a == AZ_r_a) {
        cout << "\n > Убедилась, что полученное Ra совпадает с Ra, отправленным на первом этапе";
    }
    else {
        cout << "\n ERROR: Полученное Ra НЕ совпадает с Ra, отправленным на первом этапе\n\n";
        return false;
    }

    string e_k = encryptAES(AZ_r_b, SessionKey);
    cout << "\n > Зашифровала Rb сеансовым ключом K и получила Ek: " << byteArrayToHexString(reinterpret_cast<const byte*>(e_k.data()), e_k.length());
    vector <string> alice_second_str = { AZ_trent_second_str , e_k };
    cout << "\n > Отправила Бобу второе сообщение Трента и Ek";

    //БОБ

    cout << "\n\n[Этап 5] БОБ:\n";

    cout << "\n > Получил сообщения Алисы: ";
    string BZ2_trent_second_str = alice_second_str[0];
    cout << "\n    Первое сообщение Алисы (Второе сообщение Трента): " << byteArrayToHexString(reinterpret_cast<const byte*>(BZ2_trent_second_str.data()), BZ2_trent_second_str.length());
    string BZ2_e_k = alice_second_str[1];
    cout << "\n    Второе сообщение Алисы: " << byteArrayToHexString(reinterpret_cast<const byte*>(BZ2_e_k.data()), BZ2_e_k.length());

    vector <string> BZ2_trent_second_str_decrypted_vec = splitString(decryptAES(BZ2_trent_second_str, BobTrentHexKey), zn);
    string BZ2_a_name = BZ2_trent_second_str_decrypted_vec[0];
    string BZ2_K = BZ2_trent_second_str_decrypted_vec[1];
    string BZ2_t_b = BZ2_trent_second_str_decrypted_vec[2];
    cout << "\n > Расшифровал первое сообщение Алисы (Второе сообщение Трента) и узнал:";
    cout << "\n    Имя Алисы A: " << BZ2_a_name;
    cout << "\n    Сеансовый ключ K: " << BZ2_K;
    cout << "\n    Временную метку Боба Tb: " << BZ2_t_b;

    if (t_b == BZ2_t_b) {
        cout << "\n > Убедился, что полученная временная метка t_b совпадает с t_b, отправленной на втором этапе";
    }
    else {
        cout << "\n ERROR: Полученное t_b НЕ совпадает с t_b, отправленным на втором этапе\n\n";
        return false;
    }

    string BZ2_r_b = decryptAES(BZ2_e_k, BZ2_K);
    cout << "\n > Расшифровал второе сообщение Алисы сеансовым ключом K и получил Rb:" << BZ2_r_b;

    if (str_r_b == BZ2_r_b) {
        cout << "\n > Убедился, что полученное Rb совпадает с Rb, отправленным на втором этапе";
    }
    else {
        cout << "\n ERROR: Полученное Rb НЕ совпадает с Rb, отправленным на втором этапе\n\n";
        return false;
    }

    cout << "\n\n АЛИСА И БОБ УБЕДИЛИСЬ В ПОДЛИННОСТИ ДРУГ ДРУГА И ПОЛУЧИЛИ СЕКРЕТНЫЙ КЛЮЧ K = " << SessionKey;

    cout << "\n\n\n";
    if (!oneMoreVerification)
        return true;

    cout << "Проверка Алисой и Бобом подлинности друг друга без обращения к Тренту";

    //АЛИСА

    cout << "\n\n[Этап 1] АЛИСА:\n";

    cpp_int r_a1 = rand_large_by_bit_length(p);
    string str_r_a1 = boost::lexical_cast<string>(r_a1);
    cout << "\n > Сгенерировала случайное число Ra' = " << r_a1;
    cout << "\n > Имеет второе сообщение Трента, полученое на этапе 3: " << byteArrayToHexString(reinterpret_cast<const byte*>(AZ_trent_second_str.data()), AZ_trent_second_str.length());
    vector <string> alice_new_message = { AZ_trent_second_str, str_r_a1 };
    cout << "\n > Отправила Бобу второе сообщение Трента и Ra'";

    //БОБ

    cout << "\n\n[Этап 2] БОБ:\n";

    cout << "\n > Получил сообщение Алисы";
    string BZnew_trent_second_str = alice_new_message[0];
    string BZnew_r_a = alice_new_message[1];
    cpp_int r_b1 = rand_large_by_bit_length(p);
    string str_r_b1 = boost::lexical_cast<string>(r_b1);
    cout << "\n > Сгенерировал случайное число Rb' = " << str_r_b1;
    string e_k_r_a1 = encryptAES(BZnew_r_a, BZ2_K);
    cout << "\n > Зашифровал Ra' сессионным ключом K: " << byteArrayToHexString(reinterpret_cast<const byte*>(e_k_r_a1.data()), e_k_r_a1.length());
    cout << "\n > Отправил Алисе Rb' и зашифрованное Ra'";

    //АЛИСА

    cout << "\n\n[Этап 3] АЛИСА:\n";

    cout << "\n > Получила сообщение Боба";
    string AZnew_r_a1 = decryptAES(e_k_r_a1, AZ_K);
    cout << "\n > Расшифровала зашифрованное Бобом сообщение и получила Ra':" << AZnew_r_a1;
    if (AZnew_r_a1 == str_r_a1)
        cout << "\n > Убедилась, что полученное Ra' совпадает с Ra', отправленным на первом этапе";
    else {
        cout << "\n ERROR: Полученное Ra' НЕ совпадает с Ra', отправленным на первом этапе\n\n";
        return false;
    }
    string e_k_r_b1 = encryptAES(str_r_b1, AZ_K);
    cout << "\n > Зашифровала Rb' сессионным ключом K: " << byteArrayToHexString(reinterpret_cast<const byte*>(e_k_r_b1.data()), e_k_r_b1.length());
    cout << "\n > Отправила Бобу зашифрованное Rb'";

    //БОБ

    cout << "\n\n[Этап 4] БОБ:\n";

    cout << "\n > Получил сообщение Алисы";
    string BZnew_r_b1 = decryptAES(e_k_r_b1, BZ2_K);
    cout << "\n > Расшифровал зашифрованное Алисой сообщение и получил Rb':" << AZnew_r_a1;
    if (BZnew_r_b1 == str_r_b1)
        cout << "\n > Убедилась, что полученное Rb' совпадает с Rb', отправленным на втором этапе";
    else {
        cout << "\n ERROR: Полученное Rb' НЕ совпадает с Rb', отправленным на втором этапе\n\n";
        return false;
    }

    cout << "\n\n АЛИСА И БОБ УБЕДИЛИСЬ В ПОДЛИННОСТИ ДРУГ ДРУГА БЕЗ ПОМОЩИ ТРЕНТА";
    cout << "\n\n\n";
    return true;

}

int main(int argc, char* argv[]) {
    setlocale(LC_ALL, "rus");
    int p = 128;
    bool oneMoreVerification = false;
    for (int i = 0; argv[i]; i++) {
        string checkStr = string(argv[i]);
        if (findInStr(checkStr, 2) == "/h") {
            helpFunc();
            return 0;
        }
        if (checkStr.length() > 2) {
            string ifStr = findInStr(checkStr, 3);
            string subStr = checkStr.substr(3, checkStr.length());
            char symbol = ',';
            if (ifStr == "/p:") {
                p = stoi(checkStr.substr(3, checkStr.length()));
            }
            if (ifStr == "/2e") {
                oneMoreVerification = true;
            }
        }
    }
    cout << "\np = " << p << "\n";
    NeumanStubblebineVerification(p, oneMoreVerification);
    return 0;
}