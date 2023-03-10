import { Component, EventEmitter, Input, Output, ViewContainerRef } from '@angular/core';
import { currencies, Currency } from '../currencies';
import { LogService } from '../log.service'
import { FormBuilder, Validators } from '@angular/forms';
import { concatAll, from as observableFrom, Observable, of as observableOf } from 'rxjs';
import * as RX from 'rxjs';
import { ProductComponent, ProductData } from '../product/product.component';

@Component({
  selector: 'app-login',
  templateUrl: './login.component.html',
  styleUrls: ['./login.component.css']
})
export class LoginComponent {
  currencies = [...currencies]

  counter = 0

  loginForm = this.formBuilder.group({
    login: ['', Validators.required]
  });

  public accountData: {
    login: string
  } | undefined

  public curCurrency: RX.Subject<Currency> = new RX.Subject()
  actCurrency: Currency

  constructor(
    private logService: LogService,
    private formBuilder: FormBuilder,
    private viewRef: ViewContainerRef
  ) {
    this.actCurrency = currencies[0]
    this.curCurrency.next(this.actCurrency)
  }

  makeLogin() {
    if (!this.loginForm.valid) {
      alert('invalid form')
    } else {
      this.accountData = this.loginForm.value as typeof this.accountData
      (async () => {
        for await (const p of this.getProducts()) {
          const c = this.viewRef.createComponent(ProductComponent)
          c.instance.initialize(p, this.actCurrency, this.curCurrency)
          //scheduler
        }
      })()
    }
  }

  async* getProducts() {
    yield {name: 'phone', price: 100} satisfies ProductData as ProductData
    const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms))
    await sleep(1000)
    yield {name: 'tablet', price: 300} satisfies ProductData as ProductData
    for (let i = 0;; i++) {
      await sleep(2000)
      yield {name: `rnd ${i}`, price: 10 * i + i * i} satisfies ProductData as ProductData
    }
    //yield 1
    //for (let i = 0; i < 1; i++) {
    //  yield i
      //await sleep(100)
    //}
    return
  }

  changeCurrency(ev: Event) {
    const n = (ev.target as any).value as number
    const f = currencies.find((a) => a.id == n)
    if (f === undefined) {
      return
    }
    this.actCurrency = f
    this.curCurrency.next(f)
  }
}
