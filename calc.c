// Toghrul Zeynalli 251ADB087
// Compile with: gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
// Resources used: Standard C Library Documentation (man pages for strtod, dirent, sys/stat)

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <errno.h>
#include <dirent.h>
#include <sys/stat.h>

/* =========================================================================
 * 1. DATA TYPES & STRUCTURES
 * ========================================================================= */

typedef enum {
    VAL_INT,
    VAL_FLOAT
} ValueType;

typedef struct {
    ValueType type;
    union {
        long long i_val;
        double f_val;
    } u;
} Value;

typedef enum {
    TOK_EOF,
    TOK_NUMBER,
    TOK_PLUS,
    TOK_MINUS,
    TOK_STAR,
    TOK_SLASH,
    TOK_POWER,
    TOK_LPAREN,
    TOK_RPAREN,
    TOK_INVALID
} TokenType;

typedef struct {
    TokenType type;
    Value val;
    long long pos; // 1-based character index in file
} Token;

typedef struct {
    const char *text;
    long long length;
    long long cursor;
    Token current_token;
    int error_flag;
    long long error_pos;
} Parser;

/* =========================================================================
 * 2. HELPER FUNCTIONS
 * ========================================================================= */

// Custom exponentiation for 64-bit integers with non-negative exponents
static long long ipow(long long base, long long exp) {
    long long result = 1;
    while (exp > 0) {
        if (exp & 1) result *= base;
        base *= base;
        exp >>= 1;
    }
    return result;
}

static void report_error(Parser *p, long long pos) {
    if (!p->error_flag) {
        p->error_flag = 1;
        p->error_pos = pos;
    }
}

/* =========================================================================
 * 3. TOKENIZER (LEXER)
 * ========================================================================= */

/*
 * Tokenizer position tracking:
 * Cursor represents 0-based indexing into buffer text. Positions reported to 
 * user are 1-based (cursor + 1). Characters including newline '\n' and comments 
 * are counted towards the total position offset.
 */
static void next_token(Parser *p) {
    if (p->error_flag) return;

    while (p->cursor < p->length) {
        char c = p->text[p->cursor];

        // Skip spaces and tabs anywhere between tokens
        if (c == ' ' || c == '\t') {
            p->cursor++;
            continue;
        }

        // Newlines are skipped during tokenization but counted towards overall pos
        if (c == '\r' || c == '\n') {
            p->cursor++;
            continue;
        }

        long long tok_start_pos = p->cursor + 1; // 1-based index

        // Check for double star (**) or single star (*)
        if (c == '*') {
            if (p->cursor + 1 < p->length && p->text[p->cursor + 1] == '*') {
                p->cursor += 2;
                p->current_token = (Token){TOK_POWER, {VAL_INT, {.i_val = 0}}, tok_start_pos};
                return;
            }
            p->cursor++;
            p->current_token = (Token){TOK_STAR, {VAL_INT, {.i_val = 0}}, tok_start_pos};
            return;
        }

        if (c == '+') {
            p->cursor++;
            p->current_token = (Token){TOK_PLUS, {VAL_INT, {.i_val = 0}}, tok_start_pos};
            return;
        }
        if (c == '-') {
            p->cursor++;
            p->current_token = (Token){TOK_MINUS, {VAL_INT, {.i_val = 0}}, tok_start_pos};
            return;
        }
        if (c == '/') {
            p->cursor++;
            p->current_token = (Token){TOK_SLASH, {VAL_INT, {.i_val = 0}}, tok_start_pos};
            return;
        }
        if (c == '(') {
            p->cursor++;
            p->current_token = (Token){TOK_LPAREN, {VAL_INT, {.i_val = 0}}, tok_start_pos};
            return;
        }
        if (c == ')') {
            p->cursor++;
            p->current_token = (Token){TOK_RPAREN, {VAL_INT, {.i_val = 0}}, tok_start_pos};
            return;
        }

        // Parse Numbers (Integer or Float)
        if (isdigit((unsigned char)c)) {
            long long start_idx = p->cursor;
            int is_float = 0;

            while (p->cursor < p->length && isdigit((unsigned char)p->text[p->cursor])) {
                p->cursor++;
            }

            if (p->cursor < p->length && p->text[p->cursor] == '.') {
                is_float = 1;
                p->cursor++; // Skip '.'
                
                // Numbers must have digits after decimal point, otherwise invalid character
                if (p->cursor >= p->length || !isdigit((unsigned char)p->text[p->cursor])) {
                    // Rule 9: . without following digits is invalid character at '.'
                    p->current_token = (Token){TOK_INVALID, {VAL_INT, {.i_val = 0}}, p->cursor};
                    return;
                }
                while (p->cursor < p->length && isdigit((unsigned char)p->text[p->cursor])) {
                    p->cursor++;
                }
            }

            // Exponents like 1.5e3 are invalid: check if e/E immediately follows
            if (p->cursor < p->length && (p->text[p->cursor] == 'e' || p->text[p->cursor] == 'E')) {
                p->current_token = (Token){TOK_INVALID, {VAL_INT, {.i_val = 0}}, p->cursor + 1};
                return;
            }

            Value val;
            if (is_float) {
                val.type = VAL_FLOAT;
                val.u.f_val = strtod(&p->text[start_idx], NULL);
            } else {
                val.type = VAL_INT;
                val.u.i_val = strtoull(&p->text[start_idx], NULL, 10);
            }

            p->current_token = (Token){TOK_NUMBER, val, tok_start_pos};
            return;
        }

        // Invalid character found
        p->current_token = (Token){TOK_INVALID, {VAL_INT, {.i_val = 0}}, tok_start_pos};
        return;
    }

    p->current_token = (Token){TOK_EOF, {VAL_INT, {.i_val = 0}}, p->length + 1};
}

/* =========================================================================
 * 4. PARSER & GRAMMAR EVALUATION
 * ========================================================================= */

/*
 * EBNF Grammar with Recursive Descent:
 *   expr   := term { ('+' | '-') term }
 *   term   := power { ('*' | '/') power }
 *   power  := primary [ '**' power ]     (right-associative)
 *   primary:= NUMBER | '(' expr ')'
 */

static Value parse_expr(Parser *p);

static Value parse_primary(Parser *p) {
    Value res = {VAL_INT, {.i_val = 0}};
    if (p->error_flag) return res;

    Token tok = p->current_token;

    if (tok.type == TOK_NUMBER) {
        next_token(p);
        return tok.val;
    } 
    else if (tok.type == TOK_LPAREN) {
        next_token(p);
        res = parse_expr(p);
        if (p->error_flag) return res;

        if (p->current_token.type != TOK_RPAREN) {
            // Missing closing parenthesis
            report_error(p, p->current_token.pos);
            return res;
        }
        next_token(p);
        return res;
    } 
    else if (tok.type == TOK_INVALID) {
        report_error(p, tok.pos);
        return res;
    } 
    else {
        // Missing operand / unexpected token position
        report_error(p, tok.pos);
        return res;
    }
}

static Value parse_power(Parser *p) {
    Value left = parse_primary(p);
    if (p->error_flag) return left;

    if (p->current_token.type == TOK_POWER) {
        long long op_pos = p->current_token.pos;
        next_token(p);
        
        long long right_start_pos = p->current_token.pos;
        Value right = parse_power(p); // Recursive right-associativity call
        if (p->error_flag) return left;

        Value res;
        // Float Promoted Operation
        if (left.type == VAL_FLOAT || right.type == VAL_FLOAT) {
            double base = (left.type == VAL_FLOAT) ? left.u.f_val : (double)left.u.i_val;
            double exp = (right.type == VAL_FLOAT) ? right.u.f_val : (double)right.u.i_val;
            
            double ans = pow(base, exp);
            if (isnan(ans) || isinf(ans)) {
                // Float result is infinite or NaN -> report at operator position
                report_error(p, op_pos);
                return left;
            }
            res.type = VAL_FLOAT;
            res.u.f_val = ans;
        } else {
            // Integer Operation
            if (right.u.i_val < 0) {
                // Negative exponent error -> reported at start of exponent operand
                report_error(p, right_start_pos);
                return left;
            }
            res.type = VAL_INT;
            res.u.i_val = ipow(left.u.i_val, right.u.i_val);
        }
        return res;
    }

    return left;
}

static Value parse_term(Parser *p) {
    Value left = parse_power(p);
    if (p->error_flag) return left;

    while (p->current_token.type == TOK_STAR || p->current_token.type == TOK_SLASH) {
        TokenType op = p->current_token.type;
        next_token(p);

        long long right_start_pos = p->current_token.pos;
        Value right = parse_power(p);
        if (p->error_flag) return left;

        if (op == TOK_STAR) {
            if (left.type == VAL_FLOAT || right.type == VAL_FLOAT) {
                double l = (left.type == VAL_FLOAT) ? left.u.f_val : (double)left.u.i_val;
                double r = (right.type == VAL_FLOAT) ? right.u.f_val : (double)right.u.i_val;
                left.type = VAL_FLOAT;
                left.u.f_val = l * r;
            } else {
                left.u.i_val = left.u.i_val * right.u.i_val;
            }
        } else { // TOK_SLASH
            if (right.type == VAL_INT && right.u.i_val == 0) {
                report_error(p, right_start_pos); // Division by zero integer
                return left;
            }
            if (right.type == VAL_FLOAT && right.u.f_val == 0.0) {
                report_error(p, right_start_pos); // Division by zero float
                return left;
            }

            if (left.type == VAL_FLOAT || right.type == VAL_FLOAT) {
                double l = (left.type == VAL_FLOAT) ? left.u.f_val : (double)left.u.i_val;
                double r = (right.type == VAL_FLOAT) ? right.u.f_val : (double)right.u.i_val;
                left.type = VAL_FLOAT;
                left.u.f_val = l / r;
            } else {
                left.u.i_val = left.u.i_val / right.u.i_val; // Truncates toward zero in C
            }
        }
    }

    return left;
}

static Value parse_expr(Parser *p) {
    Value left = parse_term(p);
    if (p->error_flag) return left;

    while (p->current_token.type == TOK_PLUS || p->current_token.type == TOK_MINUS) {
        TokenType op = p->current_token.type;
        next_token(p);

        Value right = parse_term(p);
        if (p->error_flag) return left;

        if (op == TOK_PLUS) {
            if (left.type == VAL_FLOAT || right.type == VAL_FLOAT) {
                double l = (left.type == VAL_FLOAT) ? left.u.f_val : (double)left.u.i_val;
                double r = (right.type == VAL_FLOAT) ? right.u.f_val : (double)right.u.i_val;
                left.type = VAL_FLOAT;
                left.u.f_val = l + r;
            } else {
                left.u.i_val = left.u.i_val + right.u.i_val;
            }
        } else { // TOK_MINUS
            if (left.type == VAL_FLOAT || right.type == VAL_FLOAT) {
                double l = (left.type == VAL_FLOAT) ? left.u.f_val : (double)left.u.i_val;
                double r = (right.type == VAL_FLOAT) ? right.u.f_val : (double)right.u.i_val;
                left.type = VAL_FLOAT;
                left.u.f_val = l - r;
            } else {
                left.u.i_val = left.u.i_val - right.u.i_val;
            }
        }
    }

    return left;
}

/* =========================================================================
 * 5. FILE PROCESSING ENGINE
 * ========================================================================= */

static void process_file(const char *in_path, const char *out_path) {
    FILE *fin = fopen(in_path, "rb");
    if (!fin) {
        fprintf(stderr, "Error opening input file: %s\n", in_path);
        exit(1);
    }

    fseek(fin, 0, SEEK_END);
    long long sz = ftell(fin);
    fseek(fin, 0, SEEK_SET);

    char *buf = malloc(sz + 1);
    if (!buf && sz > 0) {
        fprintf(stderr, "Memory allocation failed.\n");
        fclose(fin);
        exit(1);
    }

    if (sz > 0) {
        size_t read_bytes = fread(buf, 1, sz, fin);
        if ((long long)read_bytes != sz) {
            fprintf(stderr, "Error reading file: %s\n", in_path);
            free(buf);
            fclose(fin);
            exit(1);
        }
    }
    buf[sz] = '\0';
    fclose(fin);

    // Dynamic output buffer for performance on multi-megabyte files
    size_t out_cap = 1024;
    size_t out_len = 0;
    char *out_buf = malloc(out_cap);

    long long line_start = 0;
    long long pos = 0;
    int has_error = 0;
    long long error_pos = 0;

    while (pos <= sz && !has_error) {
        if (pos == sz || buf[pos] == '\n') {
            long long line_end = pos;

            // Extract line slice
            long long idx = line_start;

            // Skip leading whitespace on line to check for comment or blank line
            while (idx < line_end && (buf[idx] == ' ' || buf[idx] == '\t' || buf[idx] == '\r')) {
                idx++;
            }

            if (idx == line_end) {
                // Blank line -> produce no output
            } else if (buf[idx] == '#') {
                // Line comment -> produce no output
            } else {
                // Parse mathematical expression in line context
                Parser p;
                p.text = buf;
                p.length = line_end; // Parse up to end of this line
                p.cursor = line_start;
                p.error_flag = 0;
                p.error_pos = 0;

                next_token(&p);
                Value val = parse_expr(&p);

                if (p.error_flag) {
                    has_error = 1;
                    error_pos = p.error_pos;
                } else if (p.current_token.type != TOK_EOF) {
                    // Extra characters remaining after parsing complete expression
                    has_error = 1;
                    error_pos = p.current_token.pos;
                } else {
                    // Format output result string
                    char tmp[128];
                    if (val.type == VAL_INT) {
                        snprintf(tmp, sizeof(tmp), "%lld\n", val.u.i_val);
                    } else {
                        snprintf(tmp, sizeof(tmp), "%.15g\n", val.u.f_val);
                    }

                    size_t tlen = strlen(tmp);
                    if (out_len + tlen + 1 > out_cap) {
                        out_cap *= 2;
                        out_buf = realloc(out_buf, out_cap);
                    }
                    memcpy(out_buf + out_len, tmp, tlen);
                    out_len += tlen;
                }
            }

            line_start = pos + 1;
        }
        pos++;
    }

    FILE *fout = fopen(out_path, "wb");
    if (!fout) {
        fprintf(stderr, "Error opening output file for writing: %s\n", out_path);
        free(buf);
        free(out_buf);
        exit(1);
    }

    if (has_error) {
        fprintf(fout, "ERROR:%lld\n", error_pos);
    } else if (out_len > 0) {
        fwrite(out_buf, 1, out_len, fout);
    }

    fclose(fout);
    free(buf);
    free(out_buf);
}

/* =========================================================================
 * 6. COMMAND-LINE INTERFACE (CLI) & MAIN ENTRY
 * ========================================================================= */

static void ensure_dir_exists(const char *dir) {
    struct stat st = {0};
    if (stat(dir, &st) == -1) {
#ifdef _WIN32
        mkdir(dir);
#else
        mkdir(dir, 0755);
#endif
    }
}

static const char *get_basename_without_ext(const char *path) {
    const char *base = strrchr(path, '/');
#ifdef _WIN32
    const char *b2 = strrchr(path, '\\');
    if (b2 && (!base || b2 > base)) base = b2;
#endif
    base = base ? base + 1 : path;

    static char buf[256];
    strncpy(buf, base, sizeof(buf) - 1);
    buf[sizeof(buf) - 1] = '\0';

    char *dot = strrchr(buf, '.');
    if (dot && strcmp(dot, ".txt") == 0) {
        *dot = '\0';
    }
    return buf;
}

int main(int argc, char *argv[]) {
    const char *dir_arg = NULL;
    const char *out_dir_arg = NULL;
    const char *input_file = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 || strcmp(argv[i], "--dir") == 0) {
            if (i + 1 < argc) dir_arg = argv[++i];
            else { fprintf(stderr, "Missing argument for %s\n", argv[i]); return 1; }
        } else if (strcmp(argv[i], "-o") == 0 || strcmp(argv[i], "--output-dir") == 0) {
            if (i + 1 < argc) out_dir_arg = argv[++i];
            else { fprintf(stderr, "Missing argument for %s\n", argv[i]); return 1; }
        } else if (argv[i][0] != '-') {
            input_file = argv[i];
        } else {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            return 1;
        }
    }

    const char *name = "toghrul";
    const char *lastname = "zeynalli";
    const char *studentid = "251ADB087"; 

    char out_dir[512];
    if (out_dir_arg) {
        snprintf(out_dir, sizeof(out_dir), "%s", out_dir_arg);
    } else {
        const char *base = dir_arg ? get_basename_without_ext(dir_arg) : (input_file ? get_basename_without_ext(input_file) : "out");
        snprintf(out_dir, sizeof(out_dir), "%s_%s_%s", base, name, studentid);
    }

    ensure_dir_exists(out_dir);

    if (dir_arg) {
        DIR *d = opendir(dir_arg);
        if (!d) {
            fprintf(stderr, "Cannot open directory: %s\n", dir_arg);
            return 1;
        }
        struct dirent *dir;
        while ((dir = readdir(d)) != NULL) {
            char *ext = strrchr(dir->d_name, '.');
            if (ext && strcmp(ext, ".txt") == 0) {
                char in_path[1024];
                snprintf(in_path, sizeof(in_path), "%s/%s", dir_arg, dir->d_name);
                
                char file_base[256];
                strncpy(file_base, dir->d_name, sizeof(file_base) - 1);
                file_base[sizeof(file_base) - 1] = '\0';
                char *dot = strrchr(file_base, '.');
                if (dot) *dot = '\0';

                char out_path[1024];
                snprintf(out_path, sizeof(out_path), "%s/%s_%s_%s_%s.txt", out_dir, file_base, name, lastname, studentid);

                process_file(in_path, out_path);
            }
        }
        closedir(d);
    } else if (input_file) {
        const char *file_base = get_basename_without_ext(input_file);
        char out_path[1024];
        snprintf(out_path, sizeof(out_path), "%s/%s_%s_%s_%s.txt", out_dir, file_base, name, lastname, studentid);
        
        process_file(input_file, out_path);
    } else {
        fprintf(stderr, "No input file or directory specified.\n");
        return 1;
    }

    return 0;
}