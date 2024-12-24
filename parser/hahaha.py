import random
import math
def parse_description_file(filename):
    """Парсим файл описания и возвращаем словарь аксиом и теорем с их описаниями."""
    descriptions = {}
    with open(filename, 'r', encoding='utf-8') as f:
        for line in f:
            id_, desc = line.strip().split(' ', 1)
            descriptions[id_] = desc
    return descriptions

def parse_model_file(filename):
    """Парсим файл модели и возвращаем список правил для преобразования в факты и правила CLIPS."""
    rules = []
    with open(filename, 'r', encoding='utf-8') as f:
        for line in f:
            condition, conclusion = line.strip().split(' => ')
            conditions = condition.split(' & ')
            rules.append((conditions, conclusion))
    return rules

def read_template_file(filename):
    text = []
    with open(filename, 'r', encoding='utf-8') as f:
        for line in f:
            text.append(line.rstrip('\n'))
    return text

def generate_clips_facts_and_rules(descriptions, rules, template):
    random.seed()
    """Генерируем факты и правила для CLIPS."""
    clips_code = template

    # Генерация правил
    n = 0
    for conditions, conclusion in rules:
        # Собираем строки для сообщения, заменяя id на описание
        condition_descs = [descriptions[id_].replace(" ", "_") for id_ in conditions]

        # Получаем описания для всех условий
        condition_str = '\n'.join([f"    (theorem (name {descriptions[id_].replace(" ", "_")}) (coef ?c{i}))" for i, id_ in enumerate(conditions, start=1)])
        
        # Формируем строку сообщения с описаниями
        condition_message = "> и <".join(condition_descs)
        conclusion_message = descriptions.get(conclusion, conclusion).replace(" ", "_")

        # Генерация рандомного коэфициента
        coef = round(random.random(), ndigits=2)

        # Составная строка коэффициентов
        coef_string = ""
        for indx in range(1, len(conditions)+1):
            coef_string += f" ?c{indx}"

        # Генерация правила
        clips_code.append(f"(defrule rule_{n}\n"
                          f"(declare (salience 20))\n"
                          f"{condition_str}\n"
                          f"    =>\n"
                          f"    (assert( appendmessage (str-cat \"Из <{condition_message}> доказали <{conclusion_message}> ({coef}*\" (min {coef_string}) \"=\"(* {coef} (min{coef_string}))\")\")))\n"
                          f"    (assert (theorem (name {conclusion_message}) (coef (* {coef} (min{coef_string})))))\n"
                          f")\n")
        n += 1

    return clips_code


def save_to_clips_file(clips_code, filename):
    """Сохраняем сгенерированные факты и правила в файл CLIPS."""
    with open(filename, 'w', encoding='utf-8') as f:
        f.write("\n".join(clips_code))

def main():
    # Пути к исходным файлам
    model_filename = 'model.txt'
    description_filename = 'description.txt'
    template_filename = 'template.clp'

    # Чтение файлов
    descriptions = parse_description_file(description_filename)
    rules = parse_model_file(model_filename)
    template = read_template_file(template_filename)
    # Генерация CLIPS кода
    clips_code = generate_clips_facts_and_rules(descriptions, rules, template)
    
    # Сохранение в файл .clp
    save_to_clips_file(clips_code, 'base.clp')

if __name__ == "__main__":
    main()