Bebryk Bot — Groq 70B + Firebase memory

1) Groq key
- Відкрий Groq Console -> API Keys.
- Створи ключ.
- Встав його в ai_settings.json:
  "api_key": "gsk_..."

2) Firebase memory
- Firebase Console -> Project settings -> Service accounts.
- Generate new private key.
- Скачаний JSON перейменуй на:
  firebase_service_account.json
- Поклади його в папку YouTubeBot поряд із bot.py.
- Firestore Database має бути створена в Firebase Console.

3) Встановити залежності
pip install -r requirements.txt

4) Тест
python bot.py --dry-run

Команди для тесту:
бот ші статус
бот пам'ять статус
бот як справи?

Важливо: не скидай нікому ai_settings.json після вставки Groq key і firebase_service_account.json.
