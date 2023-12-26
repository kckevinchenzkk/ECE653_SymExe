# taken from http://www.rosettacode.org/wiki/Tokenize_a_string_with_escaping
def token_with_escape(inpt, escape="^", separator="|"):
    """
    Issue  python -m doctest thisfile.py  to run the doctests.

    >>> print(token_with_escape('one^|uno||three^^^^|four^^^|^cuatro|'))
    ['one|uno', '', 'three^^', 'four^|cuatro', '']
    """
    result = []
    token = ""
    state = 0
    for c in inpt:
        if state == 0:
            if c == escape:
                state = 1
            elif c == separator:
                result.append(token)
                token = ""
            else:
                token += c
        elif state == 1:
            token += c
            state = 0
    result.append(token)
    return result

# if __name__ == "__main__":
#     print(token_with_escape('^a^'))
#     print(token_with_escape('||'))
#     print(token_with_escape(''))

