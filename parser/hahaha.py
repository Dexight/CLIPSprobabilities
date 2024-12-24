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

def generate_clips_facts_and_rules(descriptions, rules):
    """Генерируем факты и правила для CLIPS."""
    clips_code = []

    # Генерация фактов
    #for id_, desc in descriptions.items():
    #    clips_code.append(f"(theorem \"{desc}\")")

    # Генерация правил
    n = 0
    for conditions, conclusion in rules:
        # Собираем строки для сообщения, заменяя id на описание
        condition_descs = [descriptions[id_].replace(" ", "_") for id_ in conditions]

        # Получаем описания для всех условий
        condition_str = '\n'.join([f"    (theorem {descriptions[id_].replace(" ", "_")})" for id_ in conditions])
        
        # Формируем строку сообщения с описаниями
        condition_message = "> и <".join(condition_descs)
        conclusion_message = descriptions.get(conclusion, conclusion).replace(" ", "_")
        
        # Генерация правила
        clips_code.append(f"(defrule rule_{n}\n"
                          f"{condition_str}\n"
                          f"    =>\n"
                          f"    (assert( appendmessage \"Из <{condition_message}> доказали <{conclusion_message}>\"))\n"
                          f"    (assert (theorem {conclusion_message}))\n"
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
    
    # Чтение файлов
    descriptions = parse_description_file(description_filename)
    rules = parse_model_file(model_filename)
    
    # Генерация CLIPS кода
    clips_code = generate_clips_facts_and_rules(descriptions, rules)
    
    # Сохранение в файл .clp
    save_to_clips_file(clips_code, 'output.clp')

if __name__ == "__main__":
    main()