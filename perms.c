#include <stdlib.h>
#include <stdio.h>
#include <string.h>

void mult_perms(char* perms, char* result)
{
    // индекс входного массива
    size_t i = 0;
    // индекс текущей позиции в выходном массиве
    size_t j = 0;

    /* Отметить все левые скобки и заменить правые на помеченную
      копию символа, следующего за левой скобкой
     */
A1: while(perms[i] != '\0')
    {
        char next_symb;
        if(perms[i] == '(')
        {
            // пометить скобку
            perms[i] = perms[i] | 0x80;
            next_symb = perms[i+1];
        }
        else if(perms[i] == ')')
        {
            perms[i] = next_symb;
            perms[i] = perms[i] | 0x80;
        }
        ++i;
    }

    /* Произвести поиск слева направо.
       Все элементы помечены? - конец
     */

A2: i = 0;
    char start;
    while(perms[i] != '\0')
    {
        // элемент не помечен
        if(!(perms[i] & 0x80))
        {
            // start = первый непомеченный элемент
            start = perms[i];
            // вывести (
            result[j] = '(';
            ++j;
            // вывести start
            result[j] = start;
            ++j;
            // пометить start
            perms[i] = perms[i] | 0x80;
            goto A3;
        }
        ++i;
    }

    result[j] = '\0';
    return;

A3: ++i;
    // взять элемент без учета помеченности
    char current = perms[i] & 0x7f;
    ++i;
    /* Продвигаться вправо, пока либо не достигнут конец строки
       либо найден элемент, равный current.
       Пометить его, перейти к A3.
     */
A4: while(perms[i] != '\0')
    {
        // взять элемент без учета помеченности
        char elem = perms[i] & 0x7f;
        if(elem == current)
        {
            perms[i] = perms[i] | 0x80;
            goto A3;
        }
        ++i;
    }

A5: if(current != start)
    {
        // вывести current
        result[j] = current;
        ++j;
        i = 1;
        goto A4;
    }

    result[j] = ')';
    ++j;
    goto A2;
}

int main(void)
{
    char * line = NULL;
    size_t len = 0;
    ssize_t first_read;
    ssize_t read;

    FILE* fp = fopen("input.txt", "r");
    if (fp == NULL)
        exit(EXIT_FAILURE);

    size_t arg_size = 100;
    char* argument = (char*) malloc(arg_size);
    char * first_line = NULL;
    ssize_t first_len = 0;
    // смещение относительно начала файла в байтах
    long offset = 0;
    while ((first_read = getline(&first_line, &len, fp)) != -1)
    {
        offset += first_read;
        first_line[first_read - 1] = '\0';

        while ((read = getline(&line, &len, fp)) != -1)
        {
            /* printf("Retrieved line of length %zu:\n", read); */
            line[read-1] = '\0';

            char result[100] = "";
            if (argument != NULL)
            {
                strcpy(argument, first_line + 2);
                strcat(argument, line + 2);
                if (arg_size < first_read - 3 + read - 3)
                {
                    arg_size = first_read - 3 + read - 3;
                    argument = realloc(argument, arg_size);
                }

                mult_perms(argument, result);
                printf("%cx%c=%s\n", first_line[0], line[0], result);
            }
        }

        fseek(fp, offset, SEEK_SET);
    }
    fclose(fp);

    // buffer is reallocated on every call, no need to free inside while
    if (line)
        free(line);

    if (first_line)
        free(first_line);

    if (argument)
        free(argument);
    /* char str[] = "(acf)(bd)(abd)(ef)"; */
    /* char result[100] = ""; */
    /* mult_perms(str, result); */

    /* printf("%s\n", result); */
    return EXIT_SUCCESS;
}
