## Отношения
* Extensions (id, string)
* Traits (id, description)
* People (id, name, birthday, deathday)
* Languages (id, name)
* Compilers (id, name)
* Companies (id, name)
* Platforms (id, name)
* Influenced (Languages.id, Languages.id)
* Designed (People.id, Languages.id)
* Developed (Companies.id, Compilers.id)
* CompilesTo (Compilers.id, Platforms.id)
* HasExtension (Languages.Id, Extensions.id)
* HasTrait (Languages.Id, Traits.id)
* Implements (Compilers.id, Language.id)

## Функциональные зависимости

* в каждом отношении `id -> *`
* Extensions.string -> Extensions.id
* Traits.description -> Traits.id
* Languages.name -> Languages.id
* Compilers.name -> Compilers.id
* Companies.name -> Companies.id
* Plargorms.name -> Platforms.id