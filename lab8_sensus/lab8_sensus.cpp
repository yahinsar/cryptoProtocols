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
#include "rsa.h"
#include <base64.h>
#include <integer.h>
#include <filters.h>
#include <nbtheory.h>
#include <unordered_set>
#include <chrono>


using namespace std;
using namespace boost::multiprecision;
using namespace boost::random;
using namespace CryptoPP;

const int AES_KEY_SIZE = AES::DEFAULT_KEYLENGTH;
const int AES_BLOCK_SIZE = AES::BLOCKSIZE;
cpp_int pSize;

Integer generateMask(const Integer& N) {
    AutoSeededRandomPool rng;
    Integer r;
    do {
        r.Randomize(rng, Integer::One(), N - 1);
    } while (!RelativelyPrime(r, N));

    return r;
}

Integer blindSignature(const Integer& signature, const Integer& mask, const Integer& N) {
    return signature * mask % N;
}

Integer algEuclidExtendedInteger(Integer a, Integer b, Integer& x, Integer& y) {
    if (a == 0) {
        x = 0;
        y = 1;
        return b;
    }
    Integer xi, yi;
    Integer nod = algEuclidExtendedInteger(b % a, a, xi, yi);
    x = yi - (b / a) * xi;
    y = xi;
    return nod;
}

Integer unblindSignature(const Integer& blindedSignature, const Integer& mask, const Integer& N) {
    Integer x1, y1;
    algEuclidExtendedInteger(mask, N, x1, y1);
    if (x1 < 0)
        x1 = x1 + N;
    Integer inverse = x1;
    return blindedSignature * inverse % N;
}

Integer generateRSASign(const std::string& message, const RSA::PrivateKey& privateKey, AutoSeededRandomPool& rng) {
    RSASSA_PKCS1v15_SHA_Signer signer(privateKey);

    std::string signature;
    StringSource(message, true,
        new SignerFilter(rng, signer, new StringSink(signature))
    );

    return Integer(signature.c_str());
}

bool checkRSASign(const std::string& message, const Integer& signature, const RSA::PublicKey& publicKey) {
    RSASSA_PKCS1v15_SHA_Verifier verifier(publicKey);

    ostringstream oss;
    oss << signature;
    string signatureStr = oss.str();

    try {
        StringSource(signatureStr + message, true,
            new SignatureVerificationFilter(verifier, nullptr)
        );
        return true; // Подпись верна
    }
    catch (const SignatureVerificationFilter::SignatureVerificationFailed&) {
        return false; // Подпись неверна
    }
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

string encryptAES(const string& plainText, const string& hexKey) {
    SecByteBlock key((const byte*)hexKey.data(), AES_BLOCK_SIZE);
    ECB_Mode<AES>::Encryption encryptor;
    encryptor.SetKey(key, key.size());

    string cipherText;
    StringSource(plainText, true, new StreamTransformationFilter(encryptor, new StringSink(cipherText)));

    cpp_int decimalCipherText = 0;
    for (char c : cipherText) {
        decimalCipherText = decimalCipherText * 256 + static_cast<unsigned char>(c);
    }

    ostringstream oss;
    oss << decimalCipherText;
    return oss.str();
}

string decryptAES(const string& decimalCipherText, const string& hexKey) {

    SecByteBlock key((const byte*)hexKey.data(), AES_BLOCK_SIZE);
    ECB_Mode<AES>::Decryption decryptor;
    decryptor.SetKey(key, key.size());

    cpp_int decimalCipherTextValue(decimalCipherText);

    string cipherText;
    while (decimalCipherTextValue > 0) {
        unsigned char byte = static_cast<unsigned char>(decimalCipherTextValue % 256);
        cipherText.insert(cipherText.begin(), byte);
        decimalCipherTextValue /= 256;
    }

    string decryptedText;
    StringSource(cipherText, true, new StreamTransformationFilter(decryptor, new StringSink(decryptedText)));

    return decryptedText;
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
    cout << "\n\n/l:<length> - Битовая длина для ключа AES";
    cout << "\n\n/c:<c> - Количество кандидатов";
    cout << "\n\n/v:<v> - Количество избирателей";
    cout << "\n\n/h – информация о допустимых параметрах командной строки программы.\n";
}

string intToHexString(cpp_int K) {
    std::ostringstream stream;
    stream << std::hex << K;
    return stream.str();
}

string generateAESKeyFromK(cpp_int K) {
    string KString = intToHexString(K);
    SHA256 hash;
    byte digest[SHA256::DIGESTSIZE];
    hash.CalculateDigest(digest, (const byte*)KString.c_str(), KString.length());
    string hexKey;
    HexEncoder encoder(new StringSink(hexKey));
    encoder.Put(digest, sizeof(digest));
    encoder.MessageEnd();
    return hexKey;
}

string IntegerToString(Integer xInt) {
    ostringstream oss;
    oss << xInt;
    string xStr = oss.str();
    return xStr;
}

void printMessage(const string& message, int delaySeconds) {
    this_thread::sleep_for(chrono::seconds(delaySeconds));
    cout << "\n" << message << "\n";
}

void sensus_main(cpp_int countOfVoters, cpp_int countOfCandidates, int bitsLength) {

    AutoSeededRandomPool rng;

    //Шаг 1
    cout << "\n\tШаг 1\n";

    vector <cpp_int> legitimateVoters;
    cpp_int countOfLegitimateVoters;
    for (int i = 0; i < countOfVoters; i++)
    {
        if (generate_random(0, 1) == 0)
            legitimateVoters.push_back(i);
    }

    map <cpp_int, cpp_int> votersChoice;
    map <cpp_int, string> votersSecrets;
    cout << "\nЛегитимные избиратели: ";
    for (int i = 0; i < legitimateVoters.size(); i++) {
        votersChoice.insert(make_pair(legitimateVoters[i], -1));
        if (i == 0)
            cout << "i" << legitimateVoters[i];
        else
            cout << ", " << "i" <<legitimateVoters[i];
    }
    cout << "\n";

    cout << "\nКандидаты: ";
    for (int i = 0; i < countOfCandidates; i++) {
        if (i == 0)
            cout << i;
        else
            cout << ", " << i;
    }
    cout << "\n";

    for (int i = 0; i < legitimateVoters.size(); i++) {
        //Шаг 2 E
        cout << "\n\tШаг 2\n";
        //Номер избирателя
        cpp_int me = legitimateVoters[i];
        cout << "\n\nВнимание! Избиратель i" << me << " приступил к голосованию.\n\n";

        string eSecret = generateAESKeyFromK(rand_large_by_bit_length(bitsLength));

        cout << "Сгенерированный eSecret: " << eSecret << "\n";


        RSA::PrivateKey ePrivate;
        ePrivate.GenerateRandomWithKeySize(rng, 2048);

        RSA::PublicKey ePublic(ePrivate);
        cout << "\nИзбиратель сгенерировал себе ключи e_public и e_private\n";

        cpp_int bNum = generate_random(0, countOfCandidates - 1); //мб минус 1 не делать хз
        string B = boost::lexical_cast<string>(bNum);
        cout << "\nИзбиратель i" << me << " голосует за кандидата №" << B << "\n";
        cout << "\nСообщение B = " << B << "\n";

        //зашифровываем B
        string encryptedB = encryptAES(B, eSecret);

        Integer encryptedBInteger(encryptedB.c_str());

        cout << "Зашифрованное с помощью e_secret сообщение B: " << encryptedB << "\n";
        cpp_int encryptedBNum(encryptedB);

        //применяем ослепляющее шифрование

        // Получение модуля N из открытого ключа
        const Integer& N = ePublic.GetModulus();

        cout << "Модуль RSA для маскирования подписи: N = " << N << "\n";
        // Генерация маски
        Integer mask = generateMask(N);

        // Маскирование подписи
        Integer maskedBNum = blindSignature(encryptedBInteger, mask, N);

        cout << "Зашифрованное B после наложения слоя ослепляющего шифрования: " << maskedBNum << endl;

        string maskedB = IntegerToString(maskedBNum);

        //подписываем maskedB

        Integer signedB_EInteger = generateRSASign(maskedB, ePrivate, rng);
        signedB_EInteger = signedB_EInteger.AbsoluteValue();

        string signedB_E = IntegerToString(signedB_EInteger);

        cout << "Подписанное с помощью e_private замаскированное сообщение: " << signedB_E << "\n";

        //передали signedB регистратору V и me

        //Шаг 3
        cout << "\n\tШаг 3\n";
        cout << "\nРегистратор V принял это сообщение, а также номер избирателя\n";


        RSA::PrivateKey vPrivate;
        vPrivate.GenerateRandomWithKeySize(rng, 2048);

        RSA::PublicKey vPublic(vPrivate);

        cout << "V сгенерировал себе ключи v_public и v_private\n";

        cout << "V начинает проверку избирателя.\n";
        //Проверяет избирателя на легитимность
        bool isLegitimate = false;
        for (int j = 0; j < legitimateVoters.size(); j++) {
            if (me == legitimateVoters[j]) {
                isLegitimate = true;
                break;
            }
        }
        if (!isLegitimate) {
            cout << "\nИзбиратель i" << me << " не легитимный\n";
            continue;
        }
        if (votersChoice[me] != -1) {
            cout << "\nИзбиратель i" << me << " уже голосовал\n";
            continue;
        }
        cout << "Проверки на легитимность и на то, голосовал ли уже кандидат, пройдены\n";
        

        Integer signedB_VEInteger = generateRSASign(signedB_E, vPrivate, rng);
        signedB_VEInteger = signedB_VEInteger.AbsoluteValue();

        string signedB_VE = IntegerToString(signedB_VEInteger);

        cout << "Подписанное с помощшью v_private сообщение: " << signedB_VE << "\n";

        //передает signedB_VE обратно к избирателю E

        //шаг 4
        cout << "\n\tШаг 4\n";

        //снимаем маскирующее шифрование
        cout << "Избиратель получает сообщение от регистратора\n";

        // Демаскирование подписи
        Integer signedB_VENum_withoutMask = unblindSignature(signedB_VEInteger, mask, N);

        cout << "Сообщение после снятия маскирующего шифрования: " << signedB_VENum_withoutMask << "\n";

        //отправляем signedB_VENum_withoutMask ЦИК А

        //шаг 5
        cout << "\n\tШаг 5\n";
        string signedB_VENum_withoutMaskstr = IntegerToString(signedB_VENum_withoutMask);


        cout << "A начинает проверку подписи V и E.\n";
        bool isValidVSign = checkRSASign(signedB_E, signedB_VENum_withoutMask, vPublic); // для проверки E

        if (isValidVSign)
            cout << "Проверка V прошла успешно\n";
        else {
            cout << "Проверка V не прошла\n";
            continue;
        }

        bool isValidESign = checkRSASign(maskedB, signedB_EInteger, ePublic);

        if (isValidESign)
            cout << "Проверка E прошла успешно\n";
        else {
            cout << "Проверка E не прошла\n";
            continue;
        }

        cout << "Зашифрованное сообщение B кладется в специальный список, E получает квитанцию и может быть свободен.\n";
        votersChoice[me] = encryptedBNum;
        votersSecrets[me] = eSecret;
        //Теперь избиратель свободен

    }

    //Шаг 7
    cout << "\nA начинает расшифровывать сообщения:";
    vector <int> candidatesVoicesCount((int)countOfCandidates, 0);
    auto it = votersChoice.begin();
    for (int i = 0; i < votersChoice.size() && it != votersChoice.end(); ++i, ++it) {
        if (it->second != -1) {
            string message = boost::lexical_cast<string>(it->second);
            string decryptedAEScandidateNumber = decryptAES(message, votersSecrets[it->first]);
            cout << "\nЛегитимный избиратель i" << it->first << " проголосовал за " << decryptedAEScandidateNumber;
            cpp_int candidateNumber(decryptedAEScandidateNumber);
            if (candidateNumber >= 0 && candidateNumber < countOfCandidates)
                candidatesVoicesCount[(int)candidateNumber]++;
        }
    }

    cout << "\n\nВсем приготовиться, А проводит подсчет результатов:\n";
    printMessage("1...", 1);
    printMessage("2...", 1);
    printMessage("3...", 1);
    cout << "\nГолоса за кандидатов : \n";
    for (int i = 0; i < countOfCandidates; i++) {
        cout << "Кандидат " << i << " набрал " << candidatesVoicesCount[i] << " голосов\n";
    }
    return;
}

int main(int argc, char* argv[]) {
    setlocale(LC_ALL, "rus");

    int bitsLength;
    int pBits, qBits, nBits;
    bool isN = false;
    string aliceMessage;
    cpp_int aliceSecretMessage;
    string signInfo;
    cpp_int countOfVoters, countOfCandidates;
    for (int i = 0; argv[i]; i++) {
        string checkStr = string(argv[i]);
        if (findInStr(checkStr, 2) == "/h") {
            helpFunc();
            return 0;
        }
        if (checkStr.length() > 2) {
            string ifStr = findInStr(checkStr, 3);
            char symbol = ',';
            if (ifStr == "/c:") {
                countOfCandidates = stoi(checkStr.substr(3, checkStr.length()));
            }
            if (ifStr == "/v:") {
                countOfVoters = stoi(checkStr.substr(3, checkStr.length()));
            }
            if (ifStr == "/l:") {
                bitsLength = stoi(checkStr.substr(3, checkStr.length()));
            }
        }
    }
    sensus_main(countOfVoters, countOfCandidates, bitsLength);
    return 0;
}